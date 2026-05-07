# Copyright 2024 Adobe. All rights reserved.
# This file is licensed to you under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License. You may obtain a copy
# of the License at http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software distributed under
# the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR REPRESENTATIONS
# OF ANY KIND, either express or implied. See the License for the specific language
# governing permissions and limitations under the License.

defmodule Styler.Style.Pipes do
  @moduledoc """
  Styles pipes! In particular, don't make pipe chains of only one pipe, and some persnickety pipe chain start stuff.

  Rewrites for the following Credo rules:

    * Credo.Check.Readability.BlockPipe
    * Credo.Check.Readability.OneArityFunctionInPipe
    * Credo.Check.Readability.PipeIntoAnonymousFunctions
    * Credo.Check.Readability.SinglePipe
    * Credo.Check.Refactor.FilterCount
    * Credo.Check.Refactor.FilterFilter
    * Credo.Check.Refactor.FilterReject
    * Credo.Check.Refactor.MapInto
    * Credo.Check.Refactor.MapJoin
    * Credo.Check.Refactor.MapMap
    * Credo.Check.Refactor.PipeChainStart, excluded_functions: ["from"]
    * Credo.Check.Refactor.RejectFilter
    * Credo.Check.Refactor.RejectReject
  """

  alias Styler.Style
  alias Styler.Zipper

  @behaviour Styler.Style

  @collectable ~w(Map Keyword MapSet)a
  @enum ~w(Enum Stream)a

  # most of these values were lifted directly from credo's pipe_chain_start.ex
  @literal ~w(__block__ __aliases__ unquote)a
  @value_constructors ~w(% %{} .. ..// <<>> @ {} ^ & fn from)a
  @kernel_ops ~w(++ -- && || in - * + / > < <= >= == and or != !== === <> ! not)a
  @special_ops ~w(||| &&& <<< >>> <<~ ~>> <~ ~> <~>)a
  @special_ops @literal ++ @value_constructors ++ @kernel_ops ++ @special_ops

  def run({{:|>, _, _}, _} = zipper, ctx) do
    case fix_pipe_start(zipper) do
      {{:|>, _, _}, _} = zipper ->
        case Zipper.traverse(zipper, fn {node, meta} -> {fix_pipe(node), meta} end) do
          {{:|>, _, [{:|>, _, _}, _]}, _} = chain_zipper ->
            {:cont, find_pipe_start(chain_zipper), ctx}

          # don't un-pipe into unquotes, as some expressions are only valid as pipes
          {{:|>, _, [_, {:unquote, _, [_]}]}, _} = single_pipe_unquote_zipper ->
            {:cont, single_pipe_unquote_zipper, ctx}

          # unpipe a single pipe zipper
          {{:|>, _, [lhs, rhs]}, _} = single_pipe_zipper ->
            {fun, rhs_meta, args} = rhs
            {_, lhs_meta, _} = lhs
            lhs_line = lhs_meta[:line]
            args = args || []
            # Every branch ends with the zipper being replaced with a function call
            # `lhs |> rhs(...args)` => `rhs(lhs, ...args)`
            # The differences are just figuring out what line number updates to make
            # in order to get the following properties:
            #
            # 1. write the function call on one line if reasonable
            # 2. keep comments well behaved (by doing meta line-number gymnastics)

            # if we see multiple `->`, there's no way we can online this
            # future heuristics would include finding multiple lines
            definitively_multiline? =
              Enum.any?(args, fn
                {:fn, _, [{:->, _, _}, {:->, _, _} | _]} -> true
                {:fn, _, [{:->, _, [_, _]}]} -> true
                _ -> false
              end)

            if definitively_multiline? do
              # shift rhs up to hang out with lhs
              # 1   lhs
              # 2   |> fun(
              # 3     ...args...
              # n   )
              # =>
              # 1   fun(lhs
              # 2     ... args...
              # n-1 )

              # because there could be comments between lhs and rhs, or the dev may have a bunch of empty lines,
              # we need to calculate the distance between the two ("shift")
              rhs_line = rhs_meta[:line]
              shift = lhs_line - rhs_line
              {fun, meta, args} = Style.shift_line(rhs, shift)

              # Not going to lie, no idea why the `shift + 1` is correct but it makes tests pass ¯\_(ツ)_/¯
              rhs_max_line = Style.max_line(rhs)

              comments =
                ctx.comments
                |> Style.displace_comments(lhs_line..(rhs_line - 1)//1)
                |> Style.shift_comments(rhs_line..rhs_max_line, shift + 1)

              {:cont, Zipper.replace(single_pipe_zipper, {fun, meta, [lhs | args]}), %{ctx | comments: comments}}
            else
              # try to get everything on one line.
              # formatter will kick it back to multiple if line-length doesn't accommodate
              case Zipper.up(single_pipe_zipper) do
                # if the parent is an assignment, put it on the same line as the `=`
                {{:=, am, [{_, vm, _} = var, _single_pipe]}, _} = assignment_parent ->
                  # 1 var =
                  # 2   lhs
                  # 3   |> rhs(...args)
                  # =>
                  # 1 var = rhs(lhs, ...args)
                  oneline_assignment = Style.set_line({:=, am, [var, {fun, rhs_meta, [lhs | args]}]}, vm[:line])
                  # skip so we don't re-traverse
                  {:cont, Zipper.replace(assignment_parent, oneline_assignment), ctx}

                _ ->
                  # lhs
                  # |> rhs(...args)
                  # =>
                  # rhs(lhs, ...)
                  oneline_function_call = Style.set_line({fun, rhs_meta, [lhs | args]}, lhs_line)
                  {:cont, Zipper.replace(single_pipe_zipper, oneline_function_call), ctx}
              end
            end
        end

      non_pipe ->
        {:cont, non_pipe, ctx}
    end
  end

  # a(b |> c[, ...args])
  # The first argument to a function-looking node is a pipe.
  # Maybe pipify the whole thing?
  def run({{f, m, [{:|>, _, _} = pipe | args]}, _} = zipper, ctx) do
    parent =
      case Zipper.up(zipper) do
        {{parent, _, _}, _} -> parent
        _ -> nil
      end

    stringified = is_atom(f) && to_string(f)

    cond do
      # this is likely a macro
      # assert a |> b() |> c()
      !m[:closing] ->
        {:cont, zipper, ctx}

      # leave bools alone as they often read better coming first, like when prepended with `not`
      # [not ]is_nil(a |> b() |> c())
      stringified && (String.starts_with?(stringified, "is_") or String.ends_with?(stringified, "?")) ->
        {:cont, zipper, ctx}

      # string interpolation, module attribute assignment, or prettier bools with not
      parent in [:"::", :@, :not, :|>] ->
        {:cont, zipper, ctx}

      # double down on being good to exunit macros, and any other special ops
      # ..., do: assert(a |> b |> c)
      # not (a |> b() |> c())
      f in [:assert, :refute | @special_ops] ->
        {:cont, zipper, ctx}

      # if a |> b() |> c(), do: ...
      Enum.any?(args, &Style.do_block?/1) ->
        {:cont, zipper, ctx}

      true ->
        zipper = Zipper.replace(zipper, {:|>, m, [pipe, {f, m, args}]})
        # it's possible this is a nested function call `c(b(a |> b))`, so we should walk up the tree for de-nesting
        zipper = Zipper.up(zipper) || zipper
        # recursion ensures we get those nested function calls and any additional pipes
        run(zipper, ctx)
    end
  end

  def run(zipper, ctx), do: {:cont, zipper, ctx}

  defp fix_pipe_start({pipe, zmeta} = zipper) do
    {{:|>, pipe_meta, [lhs, rhs]}, _} = start_zipper = find_pipe_start({pipe, nil})

    if valid_pipe_start?(lhs) do
      zipper
    else
      {lhs_rewrite, new_assignment} = extract_start(lhs)

      {pipe, nil} =
        start_zipper
        |> Zipper.replace({:|>, pipe_meta, [lhs_rewrite, rhs]})
        |> Zipper.top()

      if new_assignment do
        # It's important to note that with this branch, we're no longer
        # focused on the pipe! We'll return to it in a future iteration of traverse_while
        {pipe, zmeta}
        |> Style.find_nearest_block()
        |> Zipper.insert_left(new_assignment)
        |> Zipper.left()
      else
        fix_pipe_start({pipe, zmeta})
      end
    end
  end

  defp find_pipe_start(zipper) do
    Zipper.find(zipper, fn
      {:|>, _, [{:|>, _, _}, _]} -> false
      {:|>, _, _} -> true
    end)
  end

  defp extract_start({fun, meta, [arg | args]} = lhs) do
    line = meta[:line]

    # is it a do-block macro style invocation?
    # if so, store the block result in a var and start the pipe w/ that
    if Enum.any?([arg | args], &match?([{{:__block__, _, [:do]}, _} | _], &1)) do
      # `block [foo] do ... end |> ...`
      # =======================>
      # block_result =
      #   block [foo] do
      #     ...
      #   end
      #
      # block_result
      # |> ...
      var_name =
        case fun do
          # unless will be rewritten to `if` statements in the Blocks Style
          :unless -> :if
          fun when is_atom(fun) -> fun
          {:., _, [{:__aliases__, _, _}, fun]} when is_atom(fun) -> fun
          _ -> "block"
        end

      variable = {:"#{var_name}_result", [line: line], nil}
      new_assignment = {:=, [line: line], [variable, lhs]}
      {variable, new_assignment}
    else
      # looks like it's just a normal function, so lift the first arg up into a new pipe
      # `foo(a, ...) |> ...` => `a |> foo(...) |> ...`
      #
      # If the first arg is a syntax-sugared kwl, we need to manually desugar it
      arg =
        with [{{:__block__, bm, _}, _} | _] <- arg,
             :keyword <- bm[:format],
             do: {:__block__, [line: line, closing: [line: line]], [arg]},
             else: (_ -> arg)

      {{:|>, [line: line], [arg, {fun, meta, args}]}, nil}
    end
  end

  # `pipe_chain(a, b, c)` generates the ast for `a |> b |> c`
  # the intention is to make it a little easier to see what the fix_pipe functions are matching on =)
  defmacrop pipe_chain(pm, a, b, c) do
    quote do: {:|>, _, [{:|>, unquote(pm), [unquote(a), unquote(b)]}, unquote(c)]}
  end

  # a |> fun => a |> fun()
  defp fix_pipe({:|>, m, [lhs, {fun, m2, nil}]}), do: {:|>, m, [lhs, {fun, m2, []}]}

  # a |> then(&fun(&1, d)) |> c => a |> fun(d) |> c()
  defp fix_pipe({:|>, m, [lhs, {:then, _, [{:&, _, [{fun, m2, [{:&, _, _} | args]}]}]}]} = pipe) do
    rewrite = {fun, m2, args}

    # if `&1` is referenced more than once, we have to continue using `then`
    cond do
      rewrite |> Zipper.zip() |> Zipper.any?(&match?({:&, _, _}, &1)) ->
        pipe

      fun in @special_ops ->
        # we only rewrite unary/infix operators if they're in the Kernel namespace.
        # everything else stays as-is in the `then/2` because we can't know what module they're from
        if fun in @kernel_ops,
          do: {:|>, m, [lhs, {{:., m2, [{:__aliases__, m2, [:Kernel]}, fun]}, m2, args}]},
          else: pipe

      true ->
        {:|>, m, [lhs, rewrite]}
    end
  end

  # a |> then(&fun/1) |> c => a |> fun() |> c()
  # recurses to add the `()` to `fun` as it gets unwound
  defp fix_pipe({:|>, m, [lhs, {:then, _, [{:&, _, [{:/, _, [{_, _, nil} = fun, {:__block__, _, [1]}]}]}]}]}),
    do: fix_pipe({:|>, m, [lhs, fun]})

  # Credo.Check.Readability.PipeIntoAnonymousFunctions
  # rewrite anonymous function invocation to use `then/2`
  # `a |> (& &1).() |> c()` => `a |> then(& &1) |> c()`
  defp fix_pipe({:|>, m, [lhs, {{:., m2, [{anon_fun, _, _}] = fun}, _, []}]}) when anon_fun in [:&, :fn],
    do: {:|>, m, [lhs, {:then, m2, fun}]}

  # `lhs |> Enum.sort([:asc, :desc]) |> Enum.reverse()` => `lhs |> Enum.sort(:desc | :asc)`
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., _, [{_, _, [:Enum]}, :sort]} = sort, meta, sort_args},
           {{:., _, [{_, _, [:Enum]}, :reverse]}, _, []}
         ) = node
       ) do
    case sort_args do
      [] -> {:|>, pm, [lhs, {sort, meta, [{:__block__, [line: meta[:line]], [:desc]}]}]}
      [{_, m, [:desc]}] -> {:|>, pm, [lhs, {sort, meta, [{:__block__, m, [:asc]}]}]}
      [{_, m, [:asc]}] -> {:|>, pm, [lhs, {sort, meta, [{:__block__, m, [:desc]}]}]}
      _ -> node
    end
  end

  # `lhs |> Enum.map(fun) |> Enum.intersperse(sep)` => `lhs |> Enum.map_intersperse(sep, fun)
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., dm, [{_, _, [:Enum]} = enum, :map]}, em, [fun]},
           {{:., _, [{_, _, [:Enum]}, :intersperse]}, _, [sep]}
         )
       ),
       do: {:|>, pm, [lhs, {{:., dm, [enum, :map_intersperse]}, em, [Style.set_line(sep, em[:line]), fun]}]}

  # `lhs |> Enum.reverse() |> Enum.concat(enum)` => `lhs |> Enum.reverse(enum)`
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., _, [{_, _, [:Enum]}, :reverse]} = reverse, meta, []},
           {{:., _, [{_, _, [:Enum]}, :concat]}, _, [enum]}
         )
       ),
       do: {:|>, pm, [lhs, {reverse, meta, [enum]}]}

  # `lhs |> Enum.filter(fun) |> List.first([default])` => `lhs |> Enum.find([default], fun)`
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., dm, [{_, _, [:Enum]} = enum, :filter]}, meta, [fun]},
           {{:., _, [{_, _, [:List]}, :first]}, _, default}
         )
       ),
       do: {:|>, pm, [lhs, {{:., dm, [enum, :find]}, meta, Style.set_line(default, meta[:line]) ++ [fun]}]}

  # `lhs |> Enum.reverse() |> Kernel.++(enum)` => `lhs |> Enum.reverse(enum)`
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., _, [{_, _, [:Enum]}, :reverse]} = reverse, meta, []},
           {{:., _, [{_, _, [:Kernel]}, :++]}, _, [enum]}
         )
       ),
       do: {:|>, pm, [lhs, {reverse, meta, [enum]}]}

  # `lhs |> Enum.filter(filterer) |> Enum.count()` => `lhs |> Enum.count(count)`
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., _, [{_, _, [mod]}, :filter]}, meta, [filterer]},
           {{:., _, [{_, _, [:Enum]}, :count]} = count, _, []}
         )
       )
       when mod in @enum,
       do: {:|>, pm, [lhs, {count, meta, [filterer]}]}

  # `lhs |> Enum.filter(f1) |> Enum.filter(f2)` => `lhs |> Enum.filter(fn item -> f1.(item) && f2.(item) end)`
  # (Credo.Check.Refactor.FilterFilter)
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., _, [{_, _, [:Enum]}, :filter]} = filter, fm, [f1]},
           {{:., _, [{_, _, [:Enum]}, :filter]}, _, [f2]}
         )
       ),
       do: {:|>, pm, [lhs, {filter, fm, [combined_predicate(f1, f2, :&&, fm)]}]}

  # `lhs |> Enum.reject(f1) |> Enum.reject(f2)` => `lhs |> Enum.reject(fn item -> f1.(item) || f2.(item) end)`
  # (Credo.Check.Refactor.RejectReject)
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., _, [{_, _, [:Enum]}, :reject]} = reject, fm, [f1]},
           {{:., _, [{_, _, [:Enum]}, :reject]}, _, [f2]}
         )
       ),
       do: {:|>, pm, [lhs, {reject, fm, [combined_predicate(f1, f2, :||, fm)]}]}

  # `lhs |> Enum.filter(f1) |> Enum.reject(f2)` => `lhs |> Enum.filter(fn item -> f1.(item) && !f2.(item) end)`
  # (Credo.Check.Refactor.FilterReject)
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., _, [{_, _, [:Enum]}, :filter]} = filter, fm, [f1]},
           {{:., _, [{_, _, [:Enum]}, :reject]}, _, [f2]}
         )
       ),
       do: {:|>, pm, [lhs, {filter, fm, [combined_predicate(f1, f2, :&&, fm, negate_f2: true)]}]}

  # `lhs |> Enum.reject(f1) |> Enum.filter(f2)` => `lhs |> Enum.filter(fn item -> !f1.(item) && f2.(item) end)`
  # The merged call collapses to `Enum.filter` (as Credo recommends) — `f1` was the original reject,
  # so we negate it; `f2` was the original filter, so it stays.
  # (Credo.Check.Refactor.RejectFilter)
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., _, [{_, _, [:Enum]}, :reject]}, fm, [f1]},
           {{:., _, [{_, _, [:Enum]}, :filter]} = filter, _, [f2]}
         )
       ),
       do: {:|>, pm, [lhs, {filter, fm, [combined_predicate(f1, f2, :&&, fm, negate_f1: true)]}]}

  # `lhs |> Enum.map(f1) |> Enum.map(f2)` => single `Enum.map` whose body is the inlined nested call. We seed the body
  # with a one-step pipe inside f1's slot - Styler's existing `f(pipe, args)` walk then unfolds the f2 call into the
  # rest of the pipe chain. If either side can't be cleanly inlined, f1 doesn't pipify (e.g. it inlined to an operator),
  # or f2 doesn't put its placeholder in position 1 (so the seed pipe wouldn't unfold), skip — leaving the original
  # two-map chain. (Credo.Check.Refactor.MapMap)
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., _, [{_, _, [:Enum]}, :map]} = map, fm, [f1]},
           {{:., _, [{_, _, [:Enum]}, :map]}, _, [f2]}
         ) = node
       ) do
    with true <- inlineable?(f1) and inlineable?(f2) and placeholder_in_first_position?(f2),
         item_name = iteration_var_name(f1, f2),
         false <- shadows_free_var?(item_name, f1, f2),
         item = {item_name, [line: fm[:line]], nil},
         inlined_f1 = inline_capture(f1, item, fm[:line]),
         {:|>, _, _} = f1_seed <- pipify(inlined_f1) do
      body = inline_capture(f2, f1_seed, fm[:line])
      lambda = {:fn, [closing: [line: fm[:line]], line: fm[:line]], [{:->, [line: fm[:line]], [[item], body]}]}
      {:|>, pm, [lhs, {map, fm, [lambda]}]}
    else
      _ -> node
    end
  end

  # `lhs |> Stream.map(fun) |> Stream.run()` => `lhs |> Enum.each(fun)`
  # `lhs |> Stream.each(fun) |> Stream.run()` => `lhs |> Enum.each(fun)`
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., dm, [{a, am, [:Stream]}, map_or_each]}, fm, fa},
           {{:., _, [{_, _, [:Stream]}, :run]}, _, []}
         )
       )
       when map_or_each in [:map, :each],
       do: {:|>, pm, [lhs, {{:., dm, [{a, am, [:Enum]}, :each]}, fm, fa}]}

  # `lhs |> Enum.map(mapper) |> Enum.join(joiner)` => `lhs |> Enum.map_join(joiner, mapper)`
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., dm, [{_, _, [mod]}, :map]}, em, map_args},
           {{:., _, [{_, _, [:Enum]} = enum, :join]}, _, join_args}
         )
       )
       when mod in @enum,
       do: {:|>, pm, [lhs, {{:., dm, [enum, :map_join]}, em, Style.set_line(join_args, dm[:line]) ++ map_args}]}

  # `lhs |> Enum.map(mapper) |> Enum.into(empty_map)` => `lhs |> Map.new(mapper)`
  # or
  # `lhs |> Enum.map(mapper) |> Enum.into(collectable)` => `lhs |> Enum.into(collectable, mapper)
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., dm, [{_, _, [mod]}, :map]}, em, [mapper]},
           {{:., _, [{_, _, [:Enum]}, :into]} = into, _, [collectable]}
         )
       )
       when mod in @enum do
    rhs =
      case collectable do
        {{:., _, [{_, _, [mod]}, :new]}, _, []} when mod in @collectable ->
          {{:., dm, [{:__aliases__, dm, [mod]}, :new]}, em, [mapper]}

        {:%{}, _, []} ->
          {{:., dm, [{:__aliases__, dm, [:Map]}, :new]}, em, [mapper]}

        _ ->
          {into, m, [collectable]} = Style.set_line({into, em, [collectable]}, dm[:line])
          {into, m, [collectable, mapper]}
      end

    {:|>, pm, [lhs, rhs]}
  end

  # `lhs |> Enum.map(mapper) |> Map.new()` => `lhs |> Map.new(mapper)`
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., _, [{_, _, [enum]}, :map]}, em, [mapper]},
           {{:., _, [{_, _, [mod]}, :new]} = new, _, []}
         )
       )
       when mod in @collectable and enum in @enum,
       do: {:|>, pm, [lhs, {Style.set_line(new, em[:line]), em, [mapper]}]}

  @req2 for fun <- ~w(delete get head patch post put request run), bang <- ["", "!"], do: :"#{fun}#{bang}"

  # rewrite `Keyword.merge(opt) |> Req.fun1()` to `Req.fun2(opt)` for 2 arity functions that take `opts` as a second arg
  defp fix_pipe(
         pipe_chain(
           pm,
           lhs,
           {{:., _, [{_, _, [req_or_kw]}, :merge]}, m, [kw]},
           {{:., _, [{_, _, [:Req]}, fun]} = req, _, []}
         )
       )
       when req_or_kw in [:Req, :Keyword] and fun in @req2,
       do: fix_pipe({:|>, pm, [lhs, {req, m, [kw]}]})

  # Req.new |> Req.fun1,2 -> Req.fun1,2
  # all `fun` options take the same args as `Req.new`, so it's redundant to call Req.new before them
  defp fix_pipe(
         pipe_chain(pm, lhs, {{:., _, [{_, _, [:Req]}, :new]}, m, []}, {{:., _, [{_, _, [:Req]}, fun]} = req, _, args})
       )
       when fun in @req2,
       do: {:|>, pm, [lhs, {req, m, args}]}

  defp fix_pipe(node), do: node

  defp valid_pipe_start?({op, _, _}) when op in @special_ops, do: true
  # 0-arity Module.function_call()
  defp valid_pipe_start?({{:., _, _}, _, []}), do: true
  # Exempt ecto's `from`
  defp valid_pipe_start?({{:., _, [{_, _, [:Query]}, :from]}, _, _}), do: true
  defp valid_pipe_start?({{:., _, [{_, _, [:Ecto, :Query]}, :from]}, _, _}), do: true
  # map[:foo]
  defp valid_pipe_start?({{:., _, [Access, :get]}, _, _}), do: true
  # 'char#{list} interpolation'
  defp valid_pipe_start?({{:., _, [List, :to_charlist]}, _, _}), do: true
  # n-arity Module.function_call(...args)
  defp valid_pipe_start?({{:., _, _}, _, _}), do: false
  # variable
  defp valid_pipe_start?({variable, _, nil}) when is_atom(variable), do: true
  # 0-arity function_call()
  defp valid_pipe_start?({fun, _, []}) when is_atom(fun), do: true
  # function_call(with, args) or sigils. sigils are allowed, function w/ args is not
  defp valid_pipe_start?({fun, _, _args}) when is_atom(fun), do: String.match?("#{fun}", ~r/^sigil_[a-zA-Z]$/)
  defp valid_pipe_start?(_), do: true

  # Combines two 1-arity predicates into a single anonymous function: `fn item -> f1.(item) <op> f2.(item) end`.
  # Universal form that's correct regardless of whether each predicate is a capture, an `&(...)` shortform,
  # or an explicit `fn x -> ... end`. Used by FilterFilter (op: `&&`), RejectReject (op: `||`), and
  # the mixed FilterReject / RejectFilter rules (op: `&&` with one side wrapped in `!`).
  defp combined_predicate(f1, f2, op, m, opts \\ []) do
    line = m[:line]
    item = {:item, [line: line], nil}
    call_f1 = maybe_negate(predicate_call(f1, item, line), opts[:negate_f1] == true, line)
    call_f2 = maybe_negate(predicate_call(f2, item, line), opts[:negate_f2] == true, line)
    body = {op, [line: line], [call_f1, call_f2]}
    {:fn, [closing: [line: line], line: line], [{:->, [line: line], [[item], body]}]}
  end

  defp maybe_negate(call, true, line), do: {:!, [line: line], [call]}
  defp maybe_negate(call, false, _line), do: call

  defp predicate_call(fun, arg, line) do
    {{:., [line: line], [fun]}, [closing: [line: line], line: line], [arg]}
  end

  # &Mod.fun/1 → Mod.fun(arg). The `:closing` meta is what tells Styler's `f(pipe, args)` rule
  # this is a real call (not a macro) and is safe to pipify.
  defp inline_capture(
         {:&, _, [{:/, _, [{{:., _, [{:__aliases__, _, mods}, name]}, _, []}, {:__block__, _, [1]}]}]},
         arg,
         line
       ) do
    {{:., [line: line], [{:__aliases__, [line: line], mods}, name]}, [closing: [line: line], line: line], [arg]}
  end

  # &fun/1 → fun(arg)
  defp inline_capture({:&, _, [{:/, _, [{name, _, ctx}, {:__block__, _, [1]}]}]}, arg, line)
       when is_atom(name) and is_atom(ctx) do
    {name, [closing: [line: line], line: line], [arg]}
  end

  # &expr — safe to inline iff `&1` appears exactly once, no `&n` for n > 1, and there are
  # no nested `&(...)` capture forms in the body (their `&1`s belong to a different scope).
  defp inline_capture({:&, _, [body]}, arg, _line) do
    case placeholder_uses(body) do
      {1, false, false} -> substitute_placeholder(body, arg)
      _ -> nil
    end
  end

  # `fn x -> body end` — safe to inline iff `x` appears exactly once in body, no nested `fn`/`&`
  # could shadow it, and `x` isn't `_` (which we'd be substituting into ignore-position).
  defp inline_capture({:fn, _, [{:->, _, [[{name, _, ctx}], body]}]}, arg, _line)
       when is_atom(name) and is_atom(ctx) and name != :_ do
    case fn_var_uses(body, name) do
      {1, false} -> substitute_fn_var(body, name, arg)
      _ -> nil
    end
  end

  defp inline_capture(_, _, _), do: nil

  # Mirrors the inline_capture clauses above — returns true exactly when inline_capture would succeed.
  defp inlineable?({:&, _, [{:/, _, [{{:., _, [{:__aliases__, _, _}, _]}, _, []}, {:__block__, _, [1]}]}]}), do: true

  defp inlineable?({:&, _, [{:/, _, [{name, _, ctx}, {:__block__, _, [1]}]}]}) when is_atom(name) and is_atom(ctx),
    do: true

  defp inlineable?({:&, _, [body]}), do: match?({1, false, false}, placeholder_uses(body))

  defp inlineable?({:fn, _, [{:->, _, [[{name, _, ctx}], body]}]}) when is_atom(name) and is_atom(ctx) and name != :_,
    do: match?({1, false}, fn_var_uses(body, name))

  defp inlineable?(_), do: false

  # If either side is an inline `fn x -> ...`, prefer that var name for the merged lambda - the source already named the
  # iteration value. Prefer f1's name when both are named. Otherwise, fall back to `arg1`.
  defp iteration_var_name(f1, f2), do: fn_var_name(f1) || fn_var_name(f2) || :arg1

  defp fn_var_name({:fn, _, [{:->, _, [[{name, _, ctx}], _]}]}) when is_atom(name) and is_atom(ctx) and name != :_,
    do: name

  defp fn_var_name(_), do: nil

  # The merged lambda introduces a fresh binding for `name`. If that same name appears as a free variable in either
  # side's body, it referred to a closure binding in the source - after merging, the new lambda's parameter would shadow
  # it, silently changing semantics. Conservatively report any reference to `name` outside the side's own parameter as a
  # shadow risk; refs inside a nested `fn`/`&` are technically rebindable but `inlineable?` already rejects most such
  # cases.
  defp shadows_free_var?(name, f1, f2), do: free_var_in?(name, f1) or free_var_in?(name, f2)

  defp free_var_in?(name, {:fn, _, [{:->, _, [[{param, _, ctx}], body]}]}) when is_atom(param) and is_atom(ctx),
    do: param != name and var_in_ast?(body, name)

  defp free_var_in?(name, {:&, _, [body]}), do: var_in_ast?(body, name)
  defp free_var_in?(_, _), do: false

  defp var_in_ast?(ast, name) do
    {_, found} =
      Macro.prewalk(ast, false, fn
        node, true -> {node, true}
        {var, _, ctx} = node, false when var == name and is_atom(ctx) -> {node, true}
        node, acc -> {node, acc}
      end)

    found
  end

  # The seed-pipe trick only unfolds when f2's placeholder lands in arg position 1 of an outer call.
  # If it lands in position 2+, we'd produce something like `Mod.fun(other, pipe)`, which Styler's
  # `f(pipe, args)` rule won't touch and leaves an awkward partial pipe stranded inside an arg list.
  defp placeholder_in_first_position?({:&, _, [{:/, _, _}]}), do: true

  defp placeholder_in_first_position?({:&, _, [{name, _, [{:&, _, [1]} | _]}]})
       when is_atom(name) and name not in @special_ops,
       do: true

  defp placeholder_in_first_position?({:&, _, [{{:., _, _}, _, [{:&, _, [1]} | _]}]}), do: true

  defp placeholder_in_first_position?({:fn, _, [{:->, _, [[{name, _, ctx}], {fname, _, [{var, _, vctx} | _]}]}]})
       when is_atom(name) and is_atom(ctx) and name != :_ and var == name and is_atom(vctx) and is_atom(fname) and
              fname not in @special_ops,
       do: true

  defp placeholder_in_first_position?({:fn, _, [{:->, _, [[{name, _, ctx}], {{:., _, _}, _, [{var, _, vctx} | _]}]}]})
       when is_atom(name) and is_atom(ctx) and name != :_ and var == name and is_atom(vctx),
       do: true

  defp placeholder_in_first_position?(_), do: false

  defp fn_var_uses(ast, name) do
    {_, acc} =
      Macro.prewalk(ast, {0, false}, fn
        {:fn, _, _} = node, {count, _} ->
          {node, {count, true}}

        {:&, _, _} = node, {count, _} ->
          {node, {count, true}}

        {var, _, ctx} = node, {count, has_nested} when var == name and is_atom(ctx) ->
          {node, {count + 1, has_nested}}

        node, acc ->
          {node, acc}
      end)

    acc
  end

  # Mirrors substitute_placeholder/2 — replace the var without descending into substituted `arg` or
  # into nested `fn`/`&` (which have their own scoping).
  defp substitute_fn_var({:fn, _, _} = node, _name, _arg), do: node
  defp substitute_fn_var({:&, _, _} = node, _name, _arg), do: node
  defp substitute_fn_var({var, _, ctx}, name, arg) when var == name and is_atom(ctx), do: arg

  defp substitute_fn_var({a, m, args}, name, arg) when is_list(args),
    do: {substitute_fn_var(a, name, arg), m, Enum.map(args, &substitute_fn_var(&1, name, arg))}

  defp substitute_fn_var({a, b}, name, arg), do: {substitute_fn_var(a, name, arg), substitute_fn_var(b, name, arg)}

  defp substitute_fn_var(list, name, arg) when is_list(list), do: Enum.map(list, &substitute_fn_var(&1, name, arg))

  defp substitute_fn_var(other, _name, _arg), do: other

  # Convert a nested function-call AST (e.g. `f(g(h(x), y), z)`) into pipe form (`x |> h(y) |> g(z) |> f()`).
  # Stops at non-call nodes, at operator atoms (`arg + 1` shouldn't become `arg |> +(1)`), and at
  # already-piped subtrees (which are already in the desired shape).
  defp pipify({:|>, _, _} = pipe), do: pipe

  defp pipify({{:., _, _} = dot, m, [first | rest]}), do: {:|>, [line: m[:line]], [pipify(first), {dot, m, rest}]}

  defp pipify({name, m, [first | rest]}) when is_atom(name) and is_list(rest) and name not in @special_ops,
    do: {:|>, [line: m[:line]], [pipify(first), {name, m, rest}]}

  defp pipify(other), do: other

  # Returns `{count_of_&1, saw_higher_index?, saw_nested_capture?}`. The third flag prevents us
  # from inlining cases where the body contains a nested `&(...)` — its `&1`s are scoped to that
  # inner capture, not to the body we're inlining.
  defp placeholder_uses(ast) do
    {_, acc} =
      Macro.prewalk(ast, {0, false, false}, fn
        {:&, _, [n]} = node, {count, higher, has_capture} when is_integer(n) ->
          if n == 1,
            do: {node, {count + 1, higher, has_capture}},
            else: {node, {count, true, has_capture}}

        {:&, _, [_body]} = node, {count, higher, _} ->
          {node, {count, higher, true}}

        node, acc ->
          {node, acc}
      end)

    acc
  end

  # Replaces every `&1` in `ast` with `arg`, *without* descending into the substituted-in `arg`
  # (whose `&1`s, if any, are not in our scope) or into nested `&(...)` capture forms.
  defp substitute_placeholder({:&, _, [1]}, arg), do: arg
  defp substitute_placeholder({:&, _, _} = capture, _arg), do: capture

  defp substitute_placeholder({a, m, args}, arg) when is_list(args),
    do: {substitute_placeholder(a, arg), m, Enum.map(args, &substitute_placeholder(&1, arg))}

  defp substitute_placeholder({a, b}, arg), do: {substitute_placeholder(a, arg), substitute_placeholder(b, arg)}

  defp substitute_placeholder(list, arg) when is_list(list), do: Enum.map(list, &substitute_placeholder(&1, arg))

  defp substitute_placeholder(other, _arg), do: other
end
