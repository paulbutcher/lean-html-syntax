/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import HtmlSyntaxTests.Helpers

open Html HtmlSyntax HtmlModel

/-! Each error names what is wrong and points at the syntax concerned. -/

-- Children the content model rejects.

/-- info: at `<div/>`: <p> as .html .paragraph does not admit its children: child 1, <div> as .html .flow, cannot follow the children before it -/
#guard_msgs in
#html_error (html! <p><div/></p> : Html.Node .flow)

/-- info: at `text`: <ul> as .html .flow does not admit its children: child 1, text, cannot follow the children before it -/
#guard_msgs in
#html_error (html! <ul>text</ul> : Html.Node .flow)

/-- info: at `<thead></thead>`: <table> as .html .flow does not admit its children: child 2, <thead> as .html .tableHead, cannot follow the children before it -/
#guard_msgs in
#html_error (html! <table><tbody></tbody><thead></thead></table> : Html.Node .flow)

/-- info: at `mfrac`: <mfrac> as .mathml .expr does not admit its children: they end before it is complete -/
#guard_msgs in
#html_error (html! <math><mfrac><mi>x</mi></mfrac></math> : Html.Node .phrasing)

/-- info: at `text`: <g> as .svg (.el .g) does not admit its children: child 1, text, cannot follow the children before it -/
#guard_msgs in
#html_error (html! <svg><g>text</g></svg> : Html.Node .phrasing)

/-- info: at `[Html.Node.text "x"]`: <ul> as .html .flow does not admit its children: child 2, a list of .html .phrasing, cannot follow the children before it -/
#guard_msgs in
#html_error (html! <ul><li/>{[Html.Node.text "x"]}</ul> : Html.Node .flow)

/-- info: at `div`: <div> as .html .flow cannot stand where .html .phrasing is expected -/
#guard_msgs in
#html_error (html! <div/> : Html.Node .phrasing)

-- Names.

/-- info: at `foo`: unknown HTML element <foo> (custom elements need a `-` in their name) -/
#guard_msgs in
#html_error (html! <div><foo/></div> : Html.Node .flow)

/-- info: at `div`: unknown SVG element <div> -/
#guard_msgs in
#html_error (html! <svg><div/></svg> : Html.Node .phrasing)

/-- info: at `p`: unknown MathML element <p> -/
#guard_msgs in
#html_error (html! <math><p/></math> : Html.Node .phrasing)

/-- info: at `Foo-bar`: <Foo-bar> is not a valid custom element name -/
#guard_msgs in
#html_error (html! <Foo-bar/> : Html.Node .flow)

/-- info: at `div`: </div> closes <p> -/
#guard_msgs in
#html_error (html! <p>x</div> : Html.Node .flow)

/-- info: at `x`: <br> is a void element and takes no children: write <br … /> -/
#guard_msgs in
#html_error (html! <br>x</br> : Html.Node .phrasing)

-- Attributes.

/-- info: at `disabled="yes"`: disabled is a boolean attribute: write disabled={true}, disabled={b} or a bare disabled -/
#guard_msgs in
#html_error (html! <input disabled="yes"/> : Html.Node .phrasing)

/--
info: at `onClick={()}`: html!: the payload
  Attrs
has no event support: there is no instance of EventAttr Attrs "onClick" _
-/
#guard_msgs in
#html_error (html! <button onClick={()}>x</button> : Html.Node .phrasing)

/-- info: at `onclick`: event attributes are written in camel case: onClick={…} -/
#guard_msgs in
#html_error (html! <button onclick="go()">x</button> : Html.Node .phrasing)

/-- info: at `key`: key needs a value: key={…} -/
#guard_msgs in
#html_error (html! <li key/> : Html.Node .listItem)

/-- info: at `key="b"`: the element already has a key -/
#guard_msgs in
#html_error (html! <li key="a" key="b"/> : Html.Node .listItem)

/-- info: at `textContent="a"`: textContent and innerHTML replace the element's children, so it can have no others -/
#guard_msgs in
#html_error (html! <p textContent="a">b</p> : Html.Node .flow)

/--
info: at `true`: failed to synthesize instance of type class
  ToAttrValue Bool

Hint: Type class instance resolution failures can be inspected with the `set_option trace.Meta.synthInstance true` command.
-/
#guard_msgs in
#html_error (html! <p class={true}/> : Html.Node .flow)

-- Splices.

/--
info: at `(1, 2)`: html!: this has type
  ?m.4 × ?m.6
a child {…} must be a node (Web.Node P c), a List, Array or Option of nodes, a String or a number
-/
#guard_msgs in
#html_error (html! <p>{(1, 2)}</p> : Html.Node .flow)

/-- info: at `[]`: html!: the category of this child is not known at compile time; give its type, such as ([] : List (Html.Node .flow)) -/
#guard_msgs in
#html_error (html! <ul>{[]}</ul> : Html.Node .flow)

-- An element taking any of several categories where no type says which.

/-- info: at `a`: <a> could take any of .html .phrasing, .html .flow here; give the expected type, such as (html! … : Html.Node .flow) -/
#guard_msgs in
#html_error (fun (s : String) => html! <a href="/">{s}</a>)

/-- info: at `foo`: unknown element <foo> (custom elements need a `-` in their name) -/
#guard_msgs in
#html_error (html! <foo/> : Web.Node Attrs _)

-- Where an element's payload is known only once the term around it is elaborated.

/--
info: at `onClick={()}`: html!: the payload
  Attrs
has no event support: there is no instance of EventAttr Attrs "onClick" _
-/
#guard_msgs in
#html_error (html! <ul>{["a"].map fun x => html! <li onClick={()}>{x}</li>}</ul> : Html.Node .flow)
