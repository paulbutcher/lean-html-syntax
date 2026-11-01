/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlSyntax
import Html
meta import HtmlSyntax
meta import Html

/-! `html!` builds the same trees as lean-html's tag functions, and the two nest in each other. -/

namespace HtmlSyntaxTests.LeanHtml

open Html HtmlSyntax

def viaMacro (title : String) (items : List String) : Html.Node .flow :=
  html! <section class="card">
          <h2>{title}</h2>
          <p>See <a href="/more" class="more">more</a>, or <strong>not</strong>.</p>
          <ul>{items.map fun i => html! <li>{i}</li>}</ul>
          <table><tbody><tr><td>1</td><td>2</td></tr></tbody></table>
          <input type="text" name="q" disabled/>
        </section>

def viaTags (title : String) (items : List String) : Html.Node .flow :=
  section_ (attrs := { class_ := "card" }) [
    h2 [title],
    p ["See ", a { href := "/more", class_ := "more" } ["more"], ", or ", strong ["not"], "."],
    ul (items.map fun (i : String) => (li [i] : Node .listItemOrScript)),
    table [tbody [tr [td ["1"], td ["2"]]]],
    input { type := "text", name := "q", disabled := true }]

#guard (viaMacro "T" ["a", "b"]).render == (viaTags "T" ["a", "b"]).render
#guard (viaMacro "T" []).render == (viaTags "T" []).render
#guard (viaMacro "T" ["a", "b"]).renderPretty == (viaTags "T" ["a", "b"]).renderPretty

-- Tag-function nodes splice into `html!`, and `html!` nodes stand among tag-function children.
def mixed : Html.Node .flow :=
  html! <div>{p ["from ", em ["tags"]]}<ul>{[li ["a"], html! <li>b</li>]}</ul></div>

#guard mixed.render == "<div><p>from <em>tags</em></p><ul><li>a</li><li>b</li></ul></div>"
#guard (div [html! <p>from <em>html!</em></p>, ul [li ["a"]]]).render ==
  "<div><p>from <em>html!</em></p><ul><li>a</li></ul></div>"
#guard (div [mixed]).render == "<div>" ++ mixed.render ++ "</div>"

-- A page, through `document`.
#guard (document (html! <head><title>t</title></head>) (html! <body><p>x</p></body>)).startsWith
  "<!DOCTYPE html>"

end HtmlSyntaxTests.LeanHtml
