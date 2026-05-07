# Copyright 2024 Adobe. All rights reserved.
# This file is licensed to you under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License. You may obtain a copy
# of the License at http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software distributed under
# the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR REPRESENTATIONS
# OF ANY KIND, either express or implied. See the License for the specific language
# governing permissions and limitations under the License.

defmodule Styler.Style.SingleNode do
  @moduledoc """
  Simple 1-1 rewrites all crammed into one module to make for more efficient traversals

  Credo Rules addressed:

  * Credo.Check.Consistency.ParameterPatternMatching
  * Credo.Check.Readability.LargeNumbers
  * Credo.Check.Readability.ParenthesesOnZeroArityDefs
  * Credo.Check.Readability.StringSigils
  * Credo.Check.Readability.WithSingleClause
  * Credo.Check.Refactor.CaseTrivialMatches
  * Credo.Check.Refactor.CondStatements
  * Credo.Check.Refactor.RedundantWithClauseResult
  * Credo.Check.Refactor.WithClauses
  * Credo.Check.Warning.ExpensiveEmptyEnumCheck

  Also rewrites `!is_nil(x)` (and the other `is_*` guard predicates) to `not is_nil(x)`,
  matching our existing preference for `not` over `!` on guard-style predicates.
  """

  @behaviour Styler.Style

  @closing_delimiters [~s|"|, ")", "}", "|", "]", "'", ">", "/"]

  @is_guards ~w(
    is_atom is_binary is_bitstring is_boolean is_exception is_float is_function
    is_integer is_list is_map is_map_key is_nil is_number is_pid is_port
    is_reference is_struct is_tuple
  )a

  # `|> Timex.now()` => `|> Timex.now()`
  # skip over pipes into `Timex.now/1` so that we don't accidentally rewrite it as DateTime.utc_now/1
  def run({{:|>, _, [_, {{:., _, [{:__aliases__, _, [:Timex]}, :now]}, _, []}]}, _} = zipper, ctx),
    do: {:skip, zipper, ctx}

  def run({node, meta}, ctx), do: {:cont, {style(node), meta}, ctx}

  # `!is_nil(x)` => `not is_nil(x)` (and same for the other built-in `is_*` guard predicates).
  # Style preference: `not` reads more naturally with type guards.
  defp style({:!, m, [{guard, _, _} = check]}) when guard in @is_guards, do: {:not, m, [check]}

  defp style({:assert, meta, [{:!=, _, [x, {:__block__, _, [nil]}]}]}), do: style({:assert, meta, [x]})
  # refute nilly -> assert
  defp style({:refute, meta, [{:is_nil, _, [x]}]}), do: style({:assert, meta, [x]})
  defp style({:refute, meta, [{:==, _, [x, {:__block__, _, [nil]}]}]}), do: style({:assert, meta, [x]})
  # boolean ops and assert hurt my brain.
  # the lone exception is `==` (... for now) ((uh, and the exception to the exception is when it's `== nil`, above))
  defp style({:refute, meta, [{:!=, m, xy}]}), do: style({:assert, meta, [{:==, m, xy}]})
  defp style({:refute, meta, [{:!==, m, xy}]}), do: style({:assert, meta, [{:===, m, xy}]})
  defp style({:refute, meta, [{:<, m, xy}]}), do: style({:assert, meta, [{:>=, m, xy}]})
  defp style({:refute, meta, [{:<=, m, xy}]}), do: style({:assert, meta, [{:>, m, xy}]})
  defp style({:refute, meta, [{:>, m, xy}]}), do: style({:assert, meta, [{:<=, m, xy}]})
  defp style({:refute, meta, [{:>=, m, xy}]}), do: style({:assert, meta, [{:<, m, xy}]})

  # `assert x not in y` reads more naturally than `refute x in y`, so leave it alone (and same for refute).
  defp style({a, _, [{:not, _, [{:in, _, _}]}]} = node) when a in [:assert, :refute], do: node

  for {a, inverted} <- [{:assert, :refute}, {:refute, :assert}] do
    # invert negations
    defp style({unquote(a), meta, [{n, _, [x]}]}) when n in [:!, :not], do: style({unquote(inverted), meta, [x]})

    # assert Enum.member? -> assert in
    defp style({unquote(a), meta, [{{:., _, [{:__aliases__, _, [:Enum]}, :member?]}, _, [enum, elem]}]}),
      do: {unquote(a), meta, [{:in, [line: meta[:line]], [elem, enum]}]}

    # assert Enum.find -> assert Enum.any?
    defp style({unquote(a), meta, [{{:., a, [{:__aliases__, b, [:Enum]}, :find]}, c, [enum, fun]}]}),
      do: style({unquote(a), meta, [{{:., a, [{:__aliases__, b, [:Enum]}, :any?]}, c, [enum, fun]}]})

    # Enum.any?(x, & &1 == y) => y in x
    defp style({unquote(a) = a, m, [{{:., _, [{:__aliases__, _, [:Enum]}, :any?]}, _, [y, fun]}]} = node) do
      case fun do
        # & &1 == x
        {:&, _, [{:==, _, [{:&, _, [1]}, x]}]} -> {a, m, [{:in, [line: m[:line]], [x, y]}]}
        # & x == &1
        {:&, _, [{:==, _, [x, {:&, _, [1]}]}]} -> {a, m, [{:in, [line: m[:line]], [x, y]}]}
        # fn var -> var == x
        {:fn, _, [{:->, _, [[{var, _, nil}], {:==, _, [{var, _, nil}, x]}]}]} -> {a, m, [{:in, [line: m[:line]], [x, y]}]}
        # fn var -> x == var
        {:fn, _, [{:->, _, [[{var, _, nil}], {:==, _, [x, {var, _, nil}]}]}]} -> {a, m, [{:in, [line: m[:line]], [x, y]}]}
        _ -> node
      end
    end
  end

  # rewrite double-quote strings with >= 4 escaped double-quotes as sigils
  defp style({:__block__, [{:delimiter, ~s|"|} | meta], [string]} = node) when is_binary(string) do
    # running a regex against every double-quote delimited string literal in a codebase doesn't have too much impact
    # on adobe's internal codebase, but perhaps other codebases have way more literals where this'd have an impact?
    if string =~ ~r/".*".*".*"/ do
      # choose whichever delimiter would require the least # of escapes,
      # ties being broken by our stylish ordering of delimiters (reflected in the 1-8 values)
      {closer, _} =
        string
        |> String.codepoints()
        |> Stream.filter(&(&1 in @closing_delimiters))
        |> Stream.concat(@closing_delimiters)
        |> Enum.frequencies()
        |> Enum.min_by(fn
          {"\"", count} -> {count, 1}
          {")", count} -> {count, 2}
          {"}", count} -> {count, 3}
          {"|", count} -> {count, 4}
          {"]", count} -> {count, 5}
          {"'", count} -> {count, 6}
          {">", count} -> {count, 7}
          {"/", count} -> {count, 8}
        end)

      delimiter =
        case closer do
          ")" -> "("
          "}" -> "{"
          "]" -> "["
          ">" -> "<"
          closer -> closer
        end

      {:sigil_s, [{:delimiter, delimiter} | meta], [{:<<>>, [line: meta[:line]], [string]}, []]}
    else
      node
    end
  end

  # Add / Correct `_` location in large numbers. Formatter handles large number (>5 digits) rewrites,
  # but doesn't rewrite typos like `100_000_0`, so it's worthwhile to have Styler do this
  #
  # `?-` isn't part of the number node - it's its parent - so all numbers are positive at this point
  defp style({:__block__, meta, [number]}) when is_number(number) and number >= 10_000 do
    # Checking here rather than in the anonymous function due to compiler bug https://github.com/elixir-lang/elixir/issues/10485
    integer? = is_integer(number)

    meta =
      Keyword.update!(meta, :token, fn
        "0x" <> _ = token ->
          token

        "0b" <> _ = token ->
          token

        "0o" <> _ = token ->
          token

        token when integer? ->
          delimit(token)

        # is float
        token ->
          [int_token, decimals] = String.split(token, ".")
          "#{delimit(int_token)}.#{decimals}"
      end)

    {:__block__, meta, [number]}
  end

  ## INEFFICIENT FUNCTION REWRITES
  # Keep in mind when rewriting a `/n::pos_integer` arity function here that it should also be added
  # to the pipes rewriting rules, where it will appear as `/n-1`

  # Enum.into(enum, empty_map[, ...]) => Map.new(enum[, ...])
  defp style({{:., _, [{:__aliases__, _, [:Enum]}, :into]} = into, m, [enum, collectable | rest]} = node) do
    if replacement = replace_into(into, collectable, rest), do: {replacement, m, [enum | rest]}, else: node
  end

  # lhs |> Enum.into(%{}, ...) => lhs |> Map.new(...)
  defp style({:|>, meta, [lhs, {{:., _, [{_, _, [:Enum]}, :into]} = into, m, [collectable | rest]}]} = node) do
    if replacement = replace_into(into, collectable, rest), do: {:|>, meta, [lhs, {replacement, m, rest}]}, else: node
  end

  for m <- [:Map, :Keyword] do
    # lhs |> Map.merge(%{key: value}) => lhs |> Map.put(key, value)
    defp style({:|>, pm, [lhs, {{:., dm, [{_, _, [unquote(m)]} = module, :merge]}, m, [{:%{}, _, [{key, value}]}]}]}),
      do: {:|>, pm, [lhs, {{:., dm, [module, :put]}, m, [key, value]}]}

    # lhs |> Map.merge(key: value) => lhs |> Map.put(:key, value)
    defp style({:|>, pm, [lhs, {{:., dm, [{_, _, [unquote(m)]} = module, :merge]}, m, [[{key, value}]]}]}),
      do: {:|>, pm, [lhs, {{:., dm, [module, :put]}, m, [key, value]}]}

    # Map.merge(foo, %{one_key: :bar}) => Map.put(foo, :one_key, :bar)
    defp style({{:., dm, [{_, _, [unquote(m)]} = module, :merge]}, m, [lhs, {:%{}, _, [{key, value}]}]}),
      do: {{:., dm, [module, :put]}, m, [lhs, key, value]}

    # Map.merge(foo, one_key: :bar) => Map.put(foo, :one_key, :bar)
    defp style({{:., dm, [{_, _, [unquote(m)]} = module, :merge]}, m, [lhs, [{key, value}]]}),
      do: {{:., dm, [module, :put]}, m, [lhs, key, value]}

    # (lhs |>) Map.drop([key]) => Map.delete(key)
    defp style({{:., dm, [{_, _, [unquote(m)]} = module, :drop]}, m, [{:__block__, _, [[{op, _, _} = key]]}]})
         when op != :|,
         do: {{:., dm, [module, :delete]}, m, [key]}

    # Map.drop(foo, [one_key]) => Map.delete(foo, one_key)
    defp style({{:., dm, [{_, _, [unquote(m)]} = module, :drop]}, m, [lhs, {:__block__, _, [[{op, _, _} = key]]}]})
         when op != :|,
         do: {{:., dm, [module, :delete]}, m, [lhs, key]}
  end

  # Timex.now() => DateTime.utc_now()
  defp style({{:., dm, [{:__aliases__, am, [:Timex]}, :now]}, funm, []}),
    do: {{:., dm, [{:__aliases__, am, [:DateTime]}, :utc_now]}, funm, []}

  # {DateTime,NaiveDateTime,Time,Date}.compare(a, b) == :lt => {DateTime,NaiveDateTime,Time,Date}.before?(a, b)
  # {DateTime,NaiveDateTime,Time,Date}.compare(a, b) == :gt => {DateTime,NaiveDateTime,Time,Date}.after?(a, b)
  defp style({:==, _, [{{:., dm, [{:__aliases__, am, [mod]}, :compare]}, funm, args}, {:__block__, _, [result]}]})
       when mod in ~w[DateTime NaiveDateTime Time Date]a and result in [:lt, :gt] do
    fun = if result == :lt, do: :before?, else: :after?
    {{:., dm, [{:__aliases__, am, [mod]}, fun]}, funm, args}
  end

  # `length(x) <op> 0|1` => `x == []` or `x != []`. Avoids walking the whole list to check emptiness.
  # `Enum.count(x) <op> 0|1` => `Enum.empty?(x)` or `not Enum.empty?(x)` (same reason).
  # `String.length(x) <op> 0|1` => `x == ""` or `x != ""`. Avoids walking the whole string.
  # (Credo.Check.Warning.ExpensiveEmptyEnumCheck, plus the String equivalent)
  defp style({op, m, [lhs, rhs]} = ast) when op in [:==, :!=, :===, :!==, :>, :<, :>=, :<=] do
    rewrite_empty_check(op, lhs, rhs, m) || ast
  end

  # Remove parens from 0 arity funs (Credo.Check.Readability.ParenthesesOnZeroArityDefs)
  defp style({def, dm, [{fun, funm, []} | rest]}) when def in ~w(def defp)a and is_atom(fun),
    do: style({def, dm, [{fun, Keyword.delete(funm, :closing), nil} | rest]})

  defp style({def, dm, [{fun, funm, params} | rest]}) when def in ~w(def defp)a do
    {def, dm, [{fun, funm, put_matches_on_right(params)} | rest]}
  end

  # `Enum.reverse(foo) ++ bar` => `Enum.reverse(foo, bar)`
  defp style({:++, _, [{{:., _, [{_, _, [:Enum]}, :reverse]} = reverse, r_meta, [lhs]}, rhs]}),
    do: {reverse, r_meta, [lhs, rhs]}

  # ARROW REWRITES
  # `with`, `for` left arrow - if only we could write something this trivial for `->`!
  defp style({:<-, cm, [lhs, rhs]}), do: {:<-, cm, [put_matches_on_right(lhs), rhs]}
  # there's complexity to `:->` due to `cond` also utilizing the symbol but with different semantics.
  # thus, we have to have a clause for each place that `:->` can show up
  # `with` elses
  defp style({{:__block__, _, [:else]} = else_, arrows}), do: {else_, rewrite_arrows(arrows)}
  defp style({:case, cm, [head, [{do_, arrows}]]}), do: {:case, cm, [head, [{do_, rewrite_arrows(arrows)}]]}
  defp style({:fn, m, arrows}), do: {:fn, m, rewrite_arrows(arrows)}

  defp style({:to_timeout, m, [[_ | _] = args]}), do: {:to_timeout, m, [Enum.map(args, &style_to_timeout_arg/1)]}

  defp style(node), do: node

  # 1. convert plurals to singulars (`minutes` -> `minute`)
  # 2. upgrade values, eg `minute: 5 * 60` -> `hour: 5` and `minute: 60` -> `hour: 1`
  defp style_to_timeout_arg({{:__block__, m, [unit]}, value}) do
    {unit, step, next_unit} =
      case unit do
        :day -> {:day, 7, :week}
        :days -> {:day, 7, :week}
        :hour -> {:hour, 24, :day}
        :hours -> {:hour, 24, :day}
        :millisecond -> {:millisecond, 1000, :second}
        :milliseconds -> {:millisecond, 1000, :second}
        :minute -> {:minute, 60, :hour}
        :minutes -> {:minute, 60, :hour}
        :second -> {:second, 60, :minute}
        :seconds -> {:second, 60, :minute}
        :week -> {:week, :"$no_next_step", nil}
        :weeks -> {:week, :"$no_next_step", nil}
        unit -> {unit, :"$no_next_step", nil}
      end

    {unit, value} =
      case value do
        # minute: 60 -> hours: 1
        {:__block__, tm, [^step]} ->
          {next_unit, {:__block__, [token: "1", line: tm[:line]], [1]}}

        # minute: 60 * rhs -> hours: rhs
        {:*, _, [{_, _, [^step]}, rhs]} ->
          {{_, _, [next_unit]}, value} = style_to_timeout_arg({{:__block__, m, [next_unit]}, rhs})
          {next_unit, value}

        # minute: lhs * 60 -> hours: lhs
        {:*, _, [lhs, {_, _, [^step]}]} ->
          {{_, _, [next_unit]}, value} = style_to_timeout_arg({{:__block__, m, [next_unit]}, lhs})
          {next_unit, value}

        value ->
          {unit, value}
      end

    {{:__block__, m, [unit]}, value}
  end

  defp style_to_timeout_arg(other), do: other

  defp replace_into({:., dm, [{_, am, _} = enum, _]}, collectable, rest) do
    case collectable do
      {{:., _, [{_, _, [mod]}, :new]}, _, []} when mod in ~w(Map Keyword MapSet)a ->
        {:., dm, [{:__aliases__, am, [mod]}, :new]}

      {:%{}, _, []} ->
        {:., dm, [{:__aliases__, am, [:Map]}, :new]}

      {:__block__, _, [[]]} ->
        if Enum.empty?(rest), do: {:., dm, [enum, :to_list]}, else: {:., dm, [enum, :map]}

      _ ->
        nil
    end
  end

  defp rewrite_arrows(arrows) when is_list(arrows),
    do: Enum.map(arrows, fn {:->, m, [lhs, rhs]} -> {:->, m, [put_matches_on_right(lhs), rhs]} end)

  defp rewrite_arrows(macros_or_something_crazy_oh_no_abooort), do: macros_or_something_crazy_oh_no_abooort

  defp put_matches_on_right(ast) do
    Macro.prewalk(ast, fn
      # `_ = var ->` => `var ->`
      {:=, _, [{:_, _, nil}, var]} -> var
      # `var = _ ->` => `var ->`
      {:=, _, [var, {:_, _, nil}]} -> var
      # `var = *match*`  -> `*match -> var`
      {:=, m, [{_, _, nil} = var, match]} -> {:=, m, [match, var]}
      node -> node
    end)
  end

  defp delimit(token) do
    chars = String.to_charlist(token)

    result =
      case Enum.reverse(chars) do
        [hundredth, tenth, ?_ | rest] when is_integer(tenth) and is_integer(hundredth) ->
          delimited = rest |> Enum.reverse() |> fix_underscores()

          delimited ++ [?_, tenth, hundredth]

        _other_num ->
          fix_underscores(chars)
      end

    to_string(result)
  end

  defp fix_underscores(num_tokens) do
    num_tokens
    |> remove_underscores([])
    |> add_underscores([])
  end

  defp remove_underscores([?_ | rest], acc), do: remove_underscores(rest, acc)
  defp remove_underscores([digit | rest], acc), do: remove_underscores(rest, [digit | acc])
  defp remove_underscores([], reversed_list), do: reversed_list

  defp add_underscores([a, b, c, d | rest], acc), do: add_underscores([d | rest], [?_, c, b, a | acc])
  defp add_underscores(reversed_list, acc), do: Enum.reverse(reversed_list, acc)

  # ExpensiveEmptyEnumCheck helpers
  # Picks out a `length(x)` or `Enum.count(x)` call paired with a literal `0` or `1` and rewrites
  # the entire comparison. Returns nil for any shape that isn't a recognized empty-check pattern.
  defp rewrite_empty_check(op, lhs, rhs, m) do
    case {size_call(lhs), int_literal(rhs), size_call(rhs), int_literal(lhs)} do
      {kind, n, _, _} when not is_nil(kind) and not is_nil(n) -> emit_empty_check(op, kind, n, m)
      {_, _, kind, n} when not is_nil(kind) and not is_nil(n) -> emit_empty_check(swap_op(op), kind, n, m)
      _ -> nil
    end
  end

  defp size_call({:length, _, [x]}), do: {:length, x}
  defp size_call({{:., _, [{:__aliases__, _, [:Enum]}, :count]}, _, [x]}), do: {:enum_count, x}
  defp size_call({{:., _, [{:__aliases__, _, [:String]}, :length]}, _, [x]}), do: {:string_length, x}
  defp size_call(_), do: nil

  defp int_literal({:__block__, _, [n]}) when n in [0, 1], do: n
  defp int_literal(_), do: nil

  # `length(x) <= 0` is also "empty" because length is non-negative; same for `length(x) >= 0` (tautology, skip).
  defp empty_class(:==, 0), do: :empty
  defp empty_class(:===, 0), do: :empty
  defp empty_class(:!=, 0), do: :not_empty
  defp empty_class(:!==, 0), do: :not_empty
  defp empty_class(:>, 0), do: :not_empty
  defp empty_class(:<=, 0), do: :empty
  defp empty_class(:>=, 1), do: :not_empty
  defp empty_class(:<, 1), do: :empty
  defp empty_class(_, _), do: nil

  defp swap_op(:>), do: :<
  defp swap_op(:<), do: :>
  defp swap_op(:>=), do: :<=
  defp swap_op(:<=), do: :>=
  defp swap_op(op), do: op

  defp emit_empty_check(op, {:length, x}, n, m) do
    case empty_class(op, n) do
      :empty -> {:==, m, [x, {:__block__, [line: m[:line]], [[]]}]}
      :not_empty -> {:!=, m, [x, {:__block__, [line: m[:line]], [[]]}]}
      nil -> nil
    end
  end

  defp emit_empty_check(op, {:enum_count, x}, n, m) do
    empty_call = {{:., m, [{:__aliases__, m, [:Enum]}, :empty?]}, m, [x]}

    case empty_class(op, n) do
      :empty -> empty_call
      :not_empty -> {:not, m, [empty_call]}
      nil -> nil
    end
  end

  defp emit_empty_check(op, {:string_length, x}, n, m) do
    case empty_class(op, n) do
      :empty -> {:==, m, [x, {:__block__, [line: m[:line]], [""]}]}
      :not_empty -> {:!=, m, [x, {:__block__, [line: m[:line]], [""]}]}
      nil -> nil
    end
  end
end
