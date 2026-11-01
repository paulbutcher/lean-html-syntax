/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlSyntaxTests.Payload
meta import HtmlSyntaxTests.Payload

namespace HtmlSyntaxTests.Attrs

open Html HtmlSyntax HtmlModel

-- The occurrence written last wins, in the position of the first.
#guard (html! <div class="a" id="x" class="b"/> : Html.Node .flow).render ==
  "<div class=\"b\" id=\"x\"></div>"
#guard (html! <div CLASS="a" class="b"/> : Html.Node .flow).render == "<div class=\"b\"></div>"
#guard (html! <div class="a" {[.value "class" "b"]}/> : Html.Node .flow).render ==
  "<div class=\"b\"></div>"
#guard (html! <div {[.value "class" "a"]} class="b"/> : Html.Node .flow).render ==
  "<div class=\"b\"></div>"
#guard (html! <input disabled disabled={false}/> : Html.Node .phrasing).render == "<input>"
#guard (html! <input disabled={false} disabled/> : Html.Node .phrasing).render == "<input disabled>"
#guard (html! <input disabled={1 < 2}/> : Html.Node .phrasing).render == "<input disabled>"
#guard (html! <input readOnly/> : Html.Node .phrasing).render == "<input readonly>"

-- Styles become one attribute, after any written as text.
#guard (html! <div style={[("color", "red"), ("margin-left", "4px")]}/> : Html.Node .flow).render ==
  "<div style=\"color:red;margin-left:4px\"></div>"
#guard (html! <div style="a:b" style={[("c", "d")]}/> : Html.Node .flow).render ==
  "<div style=\"a:b;c:d\"></div>"
#guard (html! <div style={"a:b"}/> : Html.Node .flow).render == "<div style=\"a:b\"></div>"

-- Lasm's renamed attributes, and names with `-`, `:` and `.`.
#guard (html! <label className="c" htmlFor="i">x</label> : Html.Node .phrasing).render ==
  "<label class=\"c\" for=\"i\">x</label>"
#guard (html! <div data-x="1" hx-on:click="go()" v.b="2"/> : Html.Node .flow).render ==
  "<div data-x=\"1\" hx-on:click=\"go()\" v.b=\"2\"></div>"

-- Values of each `ToAttrValue` type.
#guard (html! <meter value={(1 : Nat)} min={(-1 : Int)} max={(2.5 : Float)}/> :
    Html.Node .phrasing).render == "<meter value=\"1\" min=\"-1\" max=\"2.500000\"></meter>"

-- `key` reaches a payload that keeps it, and lean-html-renderer's drops it.
#guard (html! <li key="k">x</li> : Html.Node .listItem).render == "<li>x</li>"
#guard (payloadOf (html! <li key={(3 : Nat)}/> : Web.Node Recorded (.html .listItem)) []).key ==
  some "3"

-- Each attribute reaches the payload in the order written.
#guard (payloadOf (html! <p a="1" b {({ attrs := [("c", "2")] } : Recorded)} style={[("d", "3")]}/> :
    Web.Node Recorded (.html .paragraph)) []).attrs ==
  [("a", "1"), ("b", ""), ("c", "2"), ("style:d", "3")]

end HtmlSyntaxTests.Attrs
