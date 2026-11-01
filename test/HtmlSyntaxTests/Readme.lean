/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlSyntaxTests.Helpers
meta import HtmlSyntax

/-! The examples in the README. -/

namespace HtmlSyntaxTests.Readme

open Html

def card (title : String) (items : List String) : Html.Node .flow :=
  html! <section class="card">
          <h2>{title}</h2>
          <ul>{items.map fun i => html! <li>{i}</li>}</ul>
        </section>

#guard (card "Hi" ["a", "b"]).render ==
  "<section class=\"card\"><h2>Hi</h2><ul><li>a</li><li>b</li></ul></section>"

def summary (n : Nat) (note : Option (Html.Node .flow)) (tags : Array String) : Html.Node .flow :=
  html! <div class="summary" data-count={n} hidden={n == 0}>
          <p>{n} items: {tags.map fun t => html! <code>{t}</code>}</p>
          {note}
          <input type="checkbox" checked disabled/>
        </div>

#guard (summary 2 none #["a", "b"]).render ==
  "<div class=\"summary\" data-count=\"2\"><p>2 items: <code>a</code><code>b</code></p>" ++
    "<input type=\"checkbox\" checked disabled></div>"

example : Html.Node .phrasing := (html! <a href="/">x</a> : Html.Node .phrasing)

/-- info: at `<div/>`: <p> as .html .paragraph does not admit its children: child 1, <div> as .html .flow, cannot follow the children before it -/
#guard_msgs in
#html_error (html! <p><div/></p> : Html.Node .flow)

#guard (html! <div style={[("color", "red"), ("margin-left", "4px")]}/> : Html.Node .flow).render ==
  "<div style=\"color:red;margin-left:4px\"></div>"

end HtmlSyntaxTests.Readme
