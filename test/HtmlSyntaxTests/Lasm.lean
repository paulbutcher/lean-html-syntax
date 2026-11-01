/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Derived from Lasm's `html!` tests (https://github.com/Millillion/lasm), released under the MIT
License:

Copyright (c) 2026 Jordan Last

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
module

import HtmlSyntaxTests.Payload
meta import HtmlSyntaxTests.Payload

/-! The cases of Lasm's `SyntaxTest.lean` that concern `html!`, against lean-html-renderer's payload,
or against `Recorded` where they concern keys and events. -/

namespace HtmlSyntaxTests.Lasm

open Html HtmlSyntax HtmlModel

def items : List Nat := [1, 2]

-- Text, whitespace, entities, numbers, unicode at the start of text.
#guard (html! <p>Hello,   world!</p> : Html.Node .flow).render == "<p>Hello, world!</p>"
#guard (html! <p>
    two
    lines
  </p> : Html.Node .flow).render == "<p>two lines</p>"
#guard (html! <p>a &amp; b &lt;c&gt; &#65;&#x42;</p> : Html.Node .flow).render ==
  "<p>a &amp; b &lt;c&gt; AB</p>"
#guard (html! <button>−</button> : Html.Node .phrasing).render == "<button>−</button>"
#guard (html! <p>✓ done</p> : Html.Node .flow).render == "<p>✓ done</p>"
#guard (html! <p><b>{(3 : Nat)}</b> items left</p> : Html.Node .flow).render ==
  "<p><b>3</b> items left</p>"
#guard (html! <p><b>x</b> <i>y</i></p> : Html.Node .flow).render == "<p><b>x</b> <i>y</i></p>"

-- Attributes, styles, keys, splices.
#guard (html! <input type="text" value={"v"} disabled /> : Html.Node .phrasing).render ==
  "<input type=\"text\" value=\"v\" disabled>"
#guard (html! <div class="a" data-id={(7 : Nat)} aria-label="l" style={[("color", "red")]}></div> :
    Html.Node .flow).render == "<div class=\"a\" data-id=\"7\" aria-label=\"l\" style=\"color:red\"></div>"
#guard (html! <div {if true then [.value "class" "on"] else []}></div> : Html.Node .flow).render ==
  "<div class=\"on\"></div>"
#guard (html! <ul>{items.map fun i => html! <li key={i}>{i}</li>}</ul> : Html.Node .flow).render ==
  "<ul><li>1</li><li>2</li></ul>"
#guard (payloadOf (html! <ul>{items.map fun i => html! <li key={i} onClick={Msg.pick i}>{i}</li>}</ul> :
    Web.Node Recorded (.html .flow)) [0]).events == ["onClick"]
#guard (payloadOf (html! <li key="k"></li> : Web.Node Recorded (.html .listItem)) []).key == some "k"

-- SVG gets its namespace; foreignObject switches back to HTML.
#guard (html! <svg><circle r="1" /></svg> : Html.Node .phrasing).erase.tag == some (.svg, "svg")
#guard (childTags (html! <svg><circle r="1" /></svg> : Html.Node .phrasing)) == [(.svg, "circle")]
#guard (childTags (html! <svg><foreignObject><div></div></foreignObject></svg> : Html.Node .phrasing)
  [0]) == [(.html, "div")]

-- Handlers receive the value given.
#guard match (payloadOf (html! <input onInput={Msg.set} /> : Web.Node Recorded (.html .phrasing)) []).input with
  | some f => match f "x" with | .set "x" => true | _ => false
  | none => false

end HtmlSyntaxTests.Lasm
