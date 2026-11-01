# Upstream gaps

What `html-syntax` needs from lean-html-model or lean-html and works around here, to be raised upstream.

## Deciding `Admits` for many children that might be whitespace (lean-html-model)

Where a content model admits inter-element whitespace, a `.one c` segment whose category whitespace widens to (flow, phrasing, and the mixtures) is shaped as optional, so that a run of them is `(c?)ⁿ`, which lean-regular's procedure decides in time that grows steeply with `n`. With the default `admits` tactic, this takes about 31 seconds, and exceeds the default heartbeat limit:

```lean
import HtmlModel
open HtmlModel Web

def d : Web.Node Unit (.html .flow) := Web.elem (.html .div) (.html .flow) () segs![]

-- 100 children: `segs![.one d, .one d, …]`
example : Web.Node Unit (.html .flow) := Web.elem (.html .div) (.html .flow) () segs![.one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d, .one d]
```

A `details` with a `summary` and 40 such children takes about 1.6 seconds, since its content model fixes an order and `Vocabulary.admits_of_kinds` does not apply.

Workaround: `html!` proves `Admits` through `admits_of_kinds` wherever the coarser shape is accepted, and otherwise checks a run of sibling elements of one category as a single `.many` segment, whose language contains the run's. Either would serve as the `admits` tactic's own first attempts; a procedure that normalised runs of optional letters would fix the cause.

## Quoting the vocabulary's types (lean-html-model)

`Web.Cat`, `Web.Elem` and the per-namespace element and category types derive `DecidableEq` and `Repr` but not `Lean.ToExpr`, which a macro needs to put a category it computed into the term it builds. `html!` derives the instances itself, in a `meta section`:

```lean
deriving instance ToExpr for HtmlModel.Html.Cat
deriving instance ToExpr for HtmlModel.Web.Cat  -- and the SVG and MathML types it nests
```

`Web.Elem.custom` holds a proof, so that no instance derives for `Web.Elem`, and `html!` quotes it by hand.

## The namespace a child's tag is read in (lean-html-model)

Nothing says in which namespace an element's children name their tags, so that `<a>` inside SVG `<text>` is SVG's `a` and `<b>` inside `<mi>` is HTML's. `html!` derives it from the categories the parent's content model admits: HTML where they are HTML's or `.any`, SVG or MathML where they are those namespaces'. An element of another namespace may be named where one of its categories widens to one of the current namespace's, as `svg` and `math` do in HTML. A function on the vocabulary saying this would keep macros in step with the model, for instance for `annotation-xml`, whose two categories read their children in different namespaces:

```lean
html! <math><semantics><mi>x</mi>
  <annotation-xml encoding="text/html"><p>HTML</p></annotation-xml></semantics></math>
```
