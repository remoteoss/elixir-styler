# Copyright 2024 Adobe. All rights reserved.
# This file is licensed to you under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License. You may obtain a copy
# of the License at http://www.apache.org/licenses/LICENSE-2.0

# Unless required by applicable law or agreed to in writing, software distributed under
# the License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR REPRESENTATIONS
# OF ANY KIND, either express or implied. See the License for the specific language
# governing permissions and limitations under the License.

defmodule Styler.Style.Defs do
  @moduledoc """
  Styles function heads so that they're as small as possible.

  The goal is that a function head fits on a single line.

  This isn't a Credo issue, and the formatter is fine with either approach. But Styler has opinions!

  Ex:

  This long declaration

      def foo(%{
        bar: baz
      }) do
        ...
      end

  Becomes

      def foo(%{bar: baz}) do
        ...
      end
  """

  alias Styler.Style
  alias Styler.Zipper

  @behaviour Styler.Style

  # Optimization / regression
  # it's non-trivial distinguishing `@def "foo"` from `def foo(...)` once you're deeper than the `@`,
  # so we're catching it here and skipping all module attribute nodes - shouldn't be defs inside them anyways
  def run({{:@, _, _}, _} = zipper, ctx), do: {:skip, zipper, ctx}

  # a def with no body like
  #
  #  def example(foo, bar \\ nil)
  #
  def run({{def, meta, [head]}, _} = zipper, ctx) when def in [:def, :defp] do
    {_fn_name, head_meta, _children} = head
    first_line = meta[:line]
    last_line = head_meta[:closing][:line]

    # Already collapsed or it's a bodyless/paramless `def fun`
    if first_line == last_line || is_nil(last_line) do
      {:skip, zipper, ctx}
    else
      comments = Style.displace_comments(ctx.comments, first_line..last_line)
      node = {def, meta, [Style.set_line(head, first_line)]}
      {:skip, Zipper.replace(zipper, node), %{ctx | comments: comments}}
    end
  end

  def run({{def, def_meta, [head, [{{:__block__, dm, [:do]}, {_, bm, _}} | _] = body]}, _} = zipper, ctx)
      when def in [:def, :defp] do
    def_line = def_meta[:line]
    end_line = def_meta[:end][:line] || bm[:closing][:line] || dm[:line]

    cond do
      def_line == end_line ->
        {:skip, zipper, ctx}

      # def do end
      Keyword.has_key?(def_meta, :do) ->
        do_line = dm[:line]
        delta = def_line - do_line

        def_meta =
          def_meta
          |> put_in([:do, :line], def_line)
          |> update_in([:end, :line], &(&1 + delta))

        head = Style.set_line(head, def_line)
        body = Style.shift_line(body, delta)
        node = {def, def_meta, [head, body]}

        comments =
          ctx.comments
          |> Style.displace_comments(def_line..do_line)
          |> Style.shift_comments(do_line..end_line, delta)

        {:skip, Zipper.replace(zipper, node), %{ctx | comments: comments}}

      # def , do:
      true ->
        node = Style.set_line({def, def_meta, [head, body]}, def_line)
        comments = Style.displace_comments(ctx.comments, def_line..end_line)
        {:skip, Zipper.replace(zipper, node), %{ctx | comments: comments}}
    end
  end

  def run(zipper, ctx), do: {:cont, zipper, ctx}
end
