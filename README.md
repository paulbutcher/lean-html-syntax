# html-syntax

A Lean 4 library providing `html!`: JSX-like markup that elaborates to [lean-html-model](https://github.com/paulbutcher/lean-html-model) nodes, with every element's children checked against its content model at compile time. With [lean-html-renderer](https://github.com/paulbutcher/lean-html-renderer)'s payload, the result is an ordinary `Html.Node cat`: it renders with that renderer and mixes freely with [lean-html](https://github.com/paulbutcher/lean-html)'s tag functions.

```lean
import HtmlSyntax
import HtmlRenderer
open Html

def card (title : String) (items : List String) : Html.Node .flow :=
  html! <section class="card">
          <h2>{title}</h2>
          <ul>{items.map fun i => html! <li>{i}</li>}</ul>
        </section>

#eval (card "Hi" ["a", "b"]).render
-- "<section class=\"card\"><h2>Hi</h2><ul><li>a</li><li>b</li></ul></section>"
```

## Installation

Add it to your `lakefile.toml`:

```toml
[[require]]
name = "html-syntax"
git = "https://github.com/paulbutcher/lean-html-syntax"
```

It depends on lean-html-model alone. To render, require [lean-html-renderer](https://github.com/paulbutcher/lean-html-renderer) too, or lean-html, which re-exports it.

## Syntax

- **Elements**: `<tag attr…>children</tag>` and `<tag attr… />`. The closing tag must match.
- **Attributes**: `name="text"`, `name={term}` where `term` has a `ToAttrValue` instance (`String`, `Nat`, `Int` and `Float`), a bare `name`, and `{term}`, which splices attributes. Names may contain `-`, `:` and `.`.
- **Text**: JSX's whitespace rules apply. Lines are trimmed, blank lines dropped and the rest joined with spaces; a run of spaces within a line becomes one. Whitespace on one line between children is kept, and whitespace containing a line break is not. `&amp;`, `&lt;`, `&gt;`, `&quot;`, `&apos;`, `&nbsp;`, `&#N;`, `&#xH;` and a few named entities such as `&mdash;` are decoded. `{"{"}` writes a brace.
- **Children**: text, elements, and `{term}`, which stands for children by its type:

| Splice type | Children |
|---|---|
| `Web.Node P c`, such as `Html.Node .listItem` | that node |
| `List (Web.Node P c)` or `Array (Web.Node P c)` | those nodes, checked as any number of `c` |
| `Option (Web.Node P c)` | that node, if any, checked as an optional `c` |
| `String`, `Nat`, `Int`, `Float` or `Char` | text |

```lean
def summary (n : Nat) (note : Option (Html.Node .flow)) (tags : Array String) : Html.Node .flow :=
  html! <div class="summary" data-count={n} hidden={n == 0}>
          <p>{n} items: {tags.map fun t => html! <code>{t}</code>}</p>
          {note}
          <input type="checkbox" checked disabled/>
        </div>
```

A list holds nodes of one category, so that a list of mixed content takes the category its members widen to, such as `List (Html.Node .flow)`; lean-html-model's coercions widen each. A splice whose category is unknown, such as `{[]}` or `{none}`, needs its type given.

## Elements and categories

Each tag is looked up with lean-html-model's `Web.Elem.ofNameIn?`, in the namespace `Web.childNamespace` says its parent's children are read in: SVG inside `<svg>`, MathML inside `<math>`, and HTML inside `foreignObject` and MathML token elements. Where nothing says which, as at the top level with no expected type, an element of any namespace may be named. A name containing `-` is a custom element, with lean-html-model's default content model. An unknown name is an error.

Each element takes a category, as in lean-html-model, chosen with its parent's content model, as `Vocabulary.infer` chooses it: `a` is phrasing content in a `<p>` and flow content holding a `<p>`, and `div` is a group of terms and descriptions in a `<dl>`. At the top level, the category comes from the expected type, which the element widens to; `html! <p>…</p>` is a `Node .flow` where one is expected. Where no type says, as inside a lambda passed to `List.map`, an element takes its only category whose content model admits its children, and an element that could take several, such as `a`, needs a type annotation: `(html! <a href="/">x</a> : Html.Node .phrasing)`.

## Content model

Children the content model rejects are a compile error, at the child concerned:

```lean
example : Html.Node .flow := html! <p><div/></p>
-- error at `<div/>`: <p> as .html .paragraph does not admit its children: child 1, <div> as
-- .html .flow, cannot follow the children before it
```

So are, each at the syntax concerned, unknown elements, children of void elements, mismatched closing tags, a boolean attribute given a string, an event attribute the payload has no instance for, and a splice of an unsupported type.

Checked: which elements may be children of which, in what order and number, as lean-html-model's content models for HTML, SVG 2 and MathML Core state them, including text and inter-element whitespace, which may stand where text may not. A list or option splice is checked for every length it could have.

Not checked, since lean-html-model does not model them: constraints on descendants rather than children, such as no interactive content inside `a`, and rules that depend on attributes, such as `link` being phrasing content only with certain attributes. `innerHTML`'s markup is not checked at all.

## Attributes and payloads

`html!` is generic over the payload `P` each element carries, through lean-html-model's `HtmlModel.HtmlPayload`:

```lean
class HtmlPayload (P : Type) where
  empty : P
  attr : String → String → P → P
  flag : String → Bool → P → P
  style : String → String → P → P
  key : String → P → P
  append : P → P → P
```

Attributes are applied in the order written:

- `name="text"` and `name={v}` are `attr name`, with `v` converted by `ToAttrValue`. `className` and `htmlFor` become `class` and `for`.
- A bare `name` is `flag name true`. `checked`, `selected`, `disabled`, `hidden`, `readonly` (or `readOnly`), `required`, `multiple`, `autofocus`, `open`, `muted`, `controls`, `autoplay`, `loop` and `novalidate` are boolean attributes, which take `{b : Bool}` and not a string.
- `key={k}` or `key="k"` is `key`, at most once per element.
- `style={[("color", c), …]}` is `style` for each property; `style="…"` and `style={s}` with `s : String` are `attr`.
- `{p}`, with `p : P`, is `append`.
- `textContent={s}` is a text child and `innerHTML={s}` a verbatim child, so that the content model and `hasVerbatim` see it. Either one, combined with other children, is an error.
- An event attribute, `on` followed by an upper-case letter such as `onClick={…}`, needs an instance of lean-html-model's `EventAttr P "onClick" α`, whose value is of type `α`; the event is named as written, so that `onEnter` may mean what its instance says. A lower-case `onclick` is an error.

lean-html-renderer's instance for its `Html.Attrs` makes a flag a bare attribute when true and nothing when false, drops `key`, and joins styles into one `style` attribute, `color:red;margin-left:4px`. A repeated name is replaced where it first appeared, so that the occurrence written last wins, as in JSX and the DOM, though the renderer would render the first; names compare as the renderer compares them, ignoring ASCII case. It has no `EventAttr` instances, so that an event attribute is an error saying that the payload has no event support.

## Elaboration time

A view of 2,001 elements in one `html!` term, as `test/Main.lean` generates it, elaborates in about a third of a second beyond loading the imports, where lean-html-model reports about 3 seconds for a term of that size. Each distinct element, category and kinds of children is proved once, as an auxiliary lemma, and reused. `lake test` budgets it, and a view whose parents hold a thousand literal children each, in units of a fixed kernel reduction timed in the same run.

## Differences from Lasm's `html!`

The macro is derived from [Lasm](https://github.com/Millillion/lasm)'s `html!`, whose surface syntax it keeps, so that Lasm can later replace its own macro with this one. It differs in what it builds and checks:

- It builds lean-html-model nodes, typed by category, rather than Lasm's untyped `Html Msg`, and checks each element's children against its content model.
- Tags are lean-html-model's, not hand-written lists, and MathML elements are checked as HTML and SVG ones are.
- Whitespace between elements is a `Web.ws` node rather than text.
- An attribute splice `{p}` takes the payload type, rather than an `Attr Msg` or a list or option of them.
- `value` is an ordinary attribute, and `textContent` and `innerHTML` are children, where Lasm sets DOM properties; a payload may treat `value` as a property itself.
- Events go through `EventAttr`, rather than Lasm's own helpers, and a payload without an instance rejects them.
- A child splice of a list or option must hold nodes of one category, and one whose category is unknown needs its type given.

## Acknowledgements

The syntax, the parser, the whitespace and entity rules, and the tests ported in `test/HtmlSyntaxTests/Lasm.lean` are derived from Lasm's `html!`, copyright (c) 2026 Jordan Last and released under the MIT License, whose notice the files concerned keep.

## License

This library is released under the Apache 2.0 license. See the LICENSE file for the complete license text.
