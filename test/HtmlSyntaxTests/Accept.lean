/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlSyntaxTests.Payload
meta import HtmlSyntaxTests.Payload

namespace HtmlSyntaxTests.Accept

open Html HtmlSyntax HtmlModel

-- An element takes its category from the expected type, widening to it.
example : Html.Node .paragraph := html! <p>x</p>
example : Html.Node .flow := html! <p>x</p>
example : Html.Node .phrasing := html! <a href="/">x</a>
example : Html.Node .flow := html! <a href="/"><p>x</p></a>

-- Where nothing says which category is wanted, an element takes the only one that admits its
-- children: `a` holding a paragraph is flow content, and `div` holding no terms is too.
example : Html.Node .flow := (html! <a href="/"><p>x</p></a> : Web.Node Attrs _)
example : Html.Node .flow := (html! <div>x</div> : Web.Node Attrs _)

-- A transparent element takes its parent's content model; `div` is a group in `dl`.
#guard (html! <p><a href="/">x <b>y</b></a></p> : Html.Node .flow).render ==
  "<p><a href=\"/\">x <b>y</b></a></p>"
#guard (html! <dl><div><dt>t</dt><dd>d</dd></div></dl> : Html.Node .flow).render ==
  "<dl><div><dt>t</dt><dd>d</dd></div></dl>"

-- Table parts in order, whitespace between them.
#guard (html! <table>
    <caption>c</caption>
    <thead><tr><th>h</th></tr></thead>
    <tbody><tr><td>a</td> <td>b</td></tr></tbody>
  </table> : Html.Node .flow).render ==
  "<table><caption>c</caption><thead><tr><th>h</th></tr></thead><tbody><tr><td>a</td> <td>b</td></tr></tbody></table>"

-- `head` holds its title and metadata in any order.
example : Html.Node .head := html! <head><meta charset="utf-8"/><title>t</title></head>

-- SVG, including `a` in text and HTML in `foreignObject`.
#guard (html! <svg viewBox="0 0 10 10">
    <g><rect width="1" height="1"/><circle r="1"/></g>
    <text>t<tspan>u</tspan><a href="/">v</a></text>
    <foreignObject><p>html</p></foreignObject>
  </svg> : Html.Node .phrasing).render ==
  "<svg viewBox=\"0 0 10 10\"><g><rect width=\"1\" height=\"1\"></rect><circle r=\"1\"></circle></g><text>t<tspan>u</tspan><a href=\"/\">v</a></text><foreignObject><p>html</p></foreignObject></svg>"
#guard (childTags (html! <svg><a><circle/></a></svg> : Html.Node .phrasing) [0]) == [(.svg, "circle")]

-- An element whose namespace nothing fixes may be of any, as in a splice into `svg`; an SVG
-- category fixes SVG, so that `a` is SVG's.
def dots (xs : List Nat) : Html.Node .phrasing :=
  html! <svg>{xs.map fun x => html! <circle cx={x} r="1"/>}</svg>

#guard (dots [1, 2]).render ==
  "<svg><circle cx=\"1\" r=\"1\"></circle><circle cx=\"2\" r=\"1\"></circle></svg>"
example : Web.Node Attrs (.svg (.el .circle)) := html! <circle r="1"/>
#guard (childTags (html! <svg>{(html! <a><circle/></a> : Web.Node Attrs (.svg .aContainer))}</svg> :
  Html.Node .phrasing) [0]) == [(.svg, "circle")]

-- MathML, with HTML in token elements and in an HTML `annotation-xml`.
#guard (html! <math><mfrac><mi>x</mi><mn>2</mn></mfrac></math> : Html.Node .phrasing).render ==
  "<math><mfrac><mi>x</mi><mn>2</mn></mfrac></math>"
#guard (childTags (html! <math><mi><b>x</b></mi></math> : Html.Node .phrasing) [0]) == [(.html, "b")]
#guard (childTags (html! <math><semantics><mi>x</mi>
    <annotation-xml encoding="text/html"><p>x</p></annotation-xml></semantics></math> :
    Html.Node .phrasing) [0, 1]) == [(.html, "p")]
#guard (childTags (html! <math><semantics><mi>x</mi>
    <annotation-xml><svg/></annotation-xml></semantics></math> :
    Html.Node .phrasing) [0, 1]) == [(.svg, "svg")]

-- Custom elements, transparent by default.
#guard (html! <div><my-card id="c"><p>x</p></my-card></div> : Html.Node .flow).render ==
  "<div><my-card id=\"c\"><p>x</p></my-card></div>"
#guard (html! <p><x-icon>i</x-icon></p> : Html.Node .flow).render == "<p><x-icon>i</x-icon></p>"

-- Each kind of splice.
def li (s : String) : Html.Node .listItem := html! <li>{s}</li>

#guard (html! <ul>{li "a"}</ul> : Html.Node .flow).render == "<ul><li>a</li></ul>"
#guard (html! <ul>{[li "a", li "b"]}</ul> : Html.Node .flow).render == "<ul><li>a</li><li>b</li></ul>"
#guard (html! <ul>{#[li "a", li "b"]}</ul> : Html.Node .flow).render == "<ul><li>a</li><li>b</li></ul>"
#guard (html! <ul>{([] : List (Html.Node .listItem))}</ul> : Html.Node .flow).render == "<ul></ul>"
#guard (html! <ul>{some (li "a")}</ul> : Html.Node .flow).render == "<ul><li>a</li></ul>"
#guard (html! <ul>{(none : Option (Html.Node .listItem))}</ul> : Html.Node .flow).render == "<ul></ul>"
#guard (html! <p>{"<s>"} {(1 : Nat)} {(-2 : Int)} {'c'}</p> : Html.Node .flow).render ==
  "<p>&lt;s&gt; 1 -2 c</p>"
#guard (html! <p>{(1.5 : Float)}</p> : Html.Node .flow).render == "<p>1.500000</p>"
#guard (html! <p>{3} and {2 + 2}</p> : Html.Node .flow).render == "<p>3 and 4</p>"
#guard (html! <p>{"{"}x{"}"}</p> : Html.Node .flow).render == "<p>{x}</p>"
#guard (html! <ul>{(html! <li>a</li>)}</ul> : Html.Node .flow).render == "<ul><li>a</li></ul>"

-- A list of nodes of a category is checked as one segment, after whitespace, among literals.
def items (xs : List String) : Html.Node .flow :=
  html! <ul class="items">
          <li>first</li> {xs.map fun x => html! <li>{x}</li>}
        </ul>

#guard (items ["a"]).render == "<ul class=\"items\"><li>first</li> <li>a</li></ul>"

-- `textContent` and `innerHTML` stand for the children; `innerHTML` is verbatim.
#guard (html! <p textContent={"a<b"}/> : Html.Node .flow).render == "<p>a&lt;b</p>"
#guard (html! <div innerHTML="<b>x</b>"/> : Html.Node .flow).render == "<div><b>x</b></div>"
#guard (html! <div innerHTML="<b>x</b>"/> : Html.Node .flow).hasVerbatim
#guard (html! <ul innerHTML="<li>x</li>"/> : Html.Node .flow).render == "<ul><li>x</li></ul>"

end HtmlSyntaxTests.Accept
