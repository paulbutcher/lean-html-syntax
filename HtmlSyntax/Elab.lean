/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Derived from Lasm's `html!` (https://github.com/Millillion/lasm), released under the MIT License:

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

public import HtmlSyntax.Parser
public import HtmlSyntax.Payload
public meta import HtmlSyntax.Text
public meta import HtmlModel
public meta import Lean.Elab.Term
public meta import Lean.Elab.SyntheticMVars
public meta import Lean.Meta.Tactic.AuxLemma
public meta import Lean.Elab.Deriving.ToExpr
public meta import Std.Data.HashMap

/-!
`html!` elaborates in three passes. The first elaborates attributes and splices, which fixes each
splice's segment by its type. The second chooses every element and category by evaluating
lean-html-model's own functions, since a transparent parent's category and its children's depend on
each other. The third builds the term, proving each distinct `Takes` and `Admits` once as an
auxiliary lemma by `decide`, checked in the kernel.
-/

public section

namespace HtmlSyntax

open Lean Elab Meta HtmlModel Regular
open Term hiding mkConst

/-- `Web.elem`'s `hc`, named so that a proof of it can be built without elaborating `∈`. -/
abbrev Takes (e : Web.Elem) (c : Web.Cat) : Prop := c ∈ Web.vocab.cats e

meta section

deriving instance ToExpr for HtmlModel.Html.Elem
deriving instance ToExpr for HtmlModel.Html.Cat
deriving instance ToExpr for HtmlModel.Svg.Elem
deriving instance ToExpr for HtmlModel.Svg.Group
deriving instance ToExpr for HtmlModel.Svg.Model
deriving instance ToExpr for HtmlModel.Svg.Cat
deriving instance ToExpr for HtmlModel.Mathml.Elem
deriving instance ToExpr for HtmlModel.Mathml.Cat
deriving instance ToExpr for HtmlModel.Web.Cat

/-- The segments `html!` produces. -/
inductive Kind where
  | one (c : Web.Cat)
  | opt (c : Web.Cat)
  | many (c : Web.Cat)

def Kind.segK : Kind → SegK Web.Cat
  | .one c => .one c
  | .opt c => .opt c
  | .many c => .many c

def Kind.toExpr : Kind → Expr
  | .one c => mkApp2 (mkConst ``SegK.one) (mkConst ``Web.Cat) (Lean.toExpr c)
  | .opt c => mkApp2 (mkConst ``SegK.opt) (mkConst ``Web.Cat) (Lean.toExpr c)
  | .many c => mkApp2 (mkConst ``SegK.many) (mkConst ``Web.Cat) (Lean.toExpr c)

def sigExpr : Expr := mkApp (mkConst ``Vocabulary.sig) (mkConst ``Web.vocab)

/-- A category as it is written in Lean, such as `.html .flow`. -/
def catName (c : Web.Cat) : String :=
  let ctor {α : Type} [Repr α] (x : α) : String :=
    "." ++ ((reprStr x).splitOn ".").getLast?.getD ""
  match c with
  | .html c => s!".html {ctor c}"
  | .mathml c => s!".mathml {ctor c}"
  | .svg (.el e) => s!".svg (.el {ctor e})"
  | .svg (.group g) => s!".svg (.group {ctor g})"
  | .svg (.content m) => s!".svg (.content {ctor m})"
  | .svg c => s!".svg {ctor c}"
  | c => ctor c

def nsName : Namespace → String
  | .html => "HTML"
  | .svg => "SVG"
  | .mathml => "MathML"

/-- An error at the syntax it concerns. -/
structure Err where
  ref : Syntax
  msg : String

/-- A child once its attributes and splices are elaborated. An element's tag is resolved later,
since the namespace it is read in depends on the category its parent takes. -/
inductive Child where
  | elem (id : Nat) (name : String) (nameStx stx : Syntax) (payload : Expr) (children : Array Child)
  /-- A child whose segment is fixed: text, whitespace, or a splice. -/
  | seg (k : Kind) (seg : Expr) (ref : Syntax) (what : String)
  /-- `innerHTML`, valid in any category, so that its category is the parent's to choose. -/
  | verbatim (s : Expr) (ref : Syntax)

def Child.ref : Child → Syntax
  | .elem _ _ _ stx .. | .seg _ _ stx _ | .verbatim _ stx => stx

def Child.isWs : Child → Bool
  | .seg (.one .ws) .. => true
  | _ => false

/-- A child with its element and category chosen. -/
inductive RChild where
  | elem (e : Web.Elem) (c : Web.Cat) (payload : Expr) (children : Array RChild) (name : String)
  | seg (k : Kind) (seg : Expr) (what : String)
  | verbatim (c : Web.Cat) (s : Expr)
  /-- Sibling elements of category `c`, as one segment. -/
  | group (c : Web.Cat) (members : Array RChild)

def RChild.kind : RChild → Kind
  | .elem _ c .. | .verbatim c _ => .one c
  | .seg k .. => k
  | .group c _ => .many c

def RChild.what : RChild → String
  | .elem _ c _ _ name => s!"<{name}> as {catName c}"
  | .seg _ _ what => what
  | .verbatim .. => "innerHTML"
  | .group c _ => s!"elements of {catName c}"

/-! ### Resolving elements and categories -/

def inNs (ns : Namespace) : Web.Cat → Bool
  | .html _ => ns == .html
  | .svg _ => ns == .svg
  | .mathml _ => ns == .mathml
  | _ => false

/-- The namespace children are read in: that of the categories the grammar admits, as the HTML
parser reads HTML wherever lean-html-model admits any element, and in MathML token elements.
`none` is any namespace, where nothing says which. -/
def childNs (g : Regex Web.Cat) (ns : Option Namespace) : Option Namespace :=
  match g.letters.find? fun c => c matches .html _ | .svg _ | .mathml _ | .any with
  | some (.html _) | some .any => some .html
  | some (.svg _) => some .svg
  | some (.mathml _) => some .mathml
  | _ => ns

def elemsNamed (name : String) : List (Namespace × Web.Elem) :=
  ((Html.Elem.ofName? name).map fun e => (.html, .html e)).toList ++
  ((Svg.Elem.ofName? name).map fun e => (.svg, .svg e)).toList ++
  ((Mathml.Elem.ofName? name).map fun e => (.mathml, .mathml e)).toList ++
  (if h : isCustomElementName name = true then [(.html, .custom name h)] else [])

/-- Whether an element of another namespace may be named where `ns` is read: one of its
categories is valid where one of `ns`'s is, as `svg` and `math` are in HTML. -/
def enters (ns : Namespace) (e : Web.Elem) : Bool :=
  (Web.vocab.cats e).any fun c => (c :: Web.Cat.above c).any (inNs ns)

def lookupElem (ns : Option Namespace) (name : String) (ref : Syntax) : Except Err Web.Elem :=
  let named := elemsNamed name
  let found : Option (Namespace × Web.Elem) := match ns with
    | some ns => (named.find? (·.1 == ns)).orElse fun _ => named.find? (enters ns ·.2)
    | none => named.head?
  match found, ns with
  | some (_, e), _ => .ok e
  | none, some .svg | none, some .mathml =>
    .error ⟨ref, s!"unknown {nsName (ns.getD .html)} element <{name}>"⟩
  | none, _ =>
    if name.contains '-' then .error ⟨ref, s!"<{name}> is not a valid custom element name"⟩
    else .error ⟨ref, s!"unknown {if ns.isSome then "HTML element" else "element"} <{name}> \
      (custom elements need a `-` in their name)"⟩

/-- Whether `e` as `c` admits children of kinds `ks` taken in any order and number, which implies
it admits `ks` and is far faster to decide where those children might be whitespace. -/
def admitsKinds (e : Web.Elem) (c : Web.Cat) (ks : List Kind) : Bool :=
  let spec := Web.vocab.spec e c
  decide (Accepts Web.vocab.widens spec.grammar
    (Shape.kinds (Web.vocab.shape spec.ws (ks.map Kind.segK))))

def admits (e : Web.Elem) (c : Web.Cat) (ks : List Kind) : Bool :=
  admitsKinds e c ks || decide (Web.vocab.Admits e c (ks.map Kind.segK))

def ordinal (children : Array Child) (i : Nat) : String :=
  let n := ((children.extract 0 i).filter (!·.isWs)).size + 1
  if (children[i]?.map Child.isWs).getD false then s!"whitespace before child {n}"
  else s!"child {n}"

def rejectionErr (name : String) (nameStx : Syntax) (e : Web.Elem) (c : Web.Cat)
    (children : Array Child) (rs : Array RChild) : Err :=
  let head := s!"<{name}> as {catName c} does not admit its children"
  match Web.vocab.rejection e c (rs.toList.map (·.kind.segK)) with
  | some (.unexpected i _) =>
    match children[i]?, rs[i]? with
    | some child, some r =>
      ⟨child.ref,
        s!"{head}: {ordinal children i}, {r.what}, cannot follow the children before it"⟩
    | _, _ => ⟨nameStx, head⟩
  | _ => ⟨nameStx, s!"{head}: they end before it is complete"⟩

/-- The category `innerHTML` takes as its parent's only child: one its parent admits. -/
def verbatimCat (e : Web.Elem) (c : Web.Cat) : Web.Cat :=
  let g := (Web.vocab.spec e c).grammar
  (g.letters.find? fun l => admits e c [.one l]).getD .text

/-- The least of `cs`, which widens to every other, as `Vocabulary.infer` chooses. -/
def least? (cs : List Web.Cat) : Option Web.Cat :=
  cs.find? fun c => cs.all (Web.vocab.widens c)

/-- Each run of sibling elements of one category as one segment. -/
def groupRuns (rs : Array RChild) : Array RChild :=
  rs.foldl (init := #[]) fun acc r =>
    match r, acc.back? with
    | .elem _ c .., some (.elem _ c' ..) | .elem _ c .., some (.group c' _) =>
      if c != c' then acc.push r else
        match acc.back? with
        | some (.group _ ms) => acc.pop.push (.group c (ms.push r))
        | some prev => acc.pop.push (.group c #[prev, r])
        | none => acc.push r
    | _, _ => acc.push r

/-- The segments `e` as `c` checks its children as, if it admits them. Where they are not in a
content model taking any order, a run of siblings of one category may become one segment, whose
language contains theirs: the kernel decides a long run of children that might be whitespace, and
so are each optional, only slowly. -/
def segmentsFor (e : Web.Elem) (c : Web.Cat) (rs : Array RChild) : Option (Array RChild) :=
  let kinds (rs : Array RChild) := rs.toList.map (·.kind)
  if admitsKinds e c (kinds rs) then some rs else
    let grouped := groupRuns rs
    if grouped.size < rs.size && admits e c (kinds grouped) then some grouped
    else if decide (Web.vocab.Admits e c ((kinds rs).map Kind.segK)) then some rs
    else none

abbrev Key := Option (Regex Web.Cat) × Option Namespace

abbrev ResolveM := StateM (Std.HashMap Nat (List (Key × Except Err RChild)))

mutual

/-- `parent` is the grammar of the parent's content model, or `none` where nothing says which
category is wanted. -/
def resolve (parent : Option (Regex Web.Cat)) (ns : Option Namespace) :
    Child → ResolveM (Except Err RChild)
  | .seg k s _ what => return .ok (.seg k s what)
  | .verbatim _ ref => return .error ⟨ref, "innerHTML has no element to stand in"⟩
  | .elem id name nameStx stx payload children => do
    let key : Key := (parent, ns)
    if let some r := ((← get).getD id []).lookup key then return r
    let r ← resolveElem parent ns name nameStx stx payload children
    modify fun m => m.insert id ((key, r) :: m.getD id [])
    return r

def resolveElem (parent : Option (Regex Web.Cat)) (ns : Option Namespace) (name : String)
    (nameStx stx : Syntax) (payload : Expr) (children : Array Child) :
    ResolveM (Except Err RChild) := do
  let e ← match lookupElem ns name nameStx with
    | .ok e => pure e
    | .error err => return .error err
  let cats := Web.vocab.cats e
  let realChildren := children.filter fun | .verbatim .. => false | _ => true
  if !realChildren.isEmpty && cats.all fun c => (Web.vocab.spec e c).grammar == .eps then
    return .error ⟨mkNullNode (realChildren.map Child.ref),
      s!"<{name}> is a void element and takes no children: write <{name} … />"⟩
  -- Each category the element may take, with its children resolved against its grammar.
  let mut tried : Array (Web.Cat × Except Err (Array RChild)) := #[]
  for c in cats do
    let g := (Web.vocab.spec e c).grammar
    let mut rs : Except Err (Array RChild) := .ok #[]
    for child in children do
      match rs with
      | .error _ => pure ()
      | .ok acc =>
        match child with
        | .verbatim s _ => rs := .ok (acc.push (.verbatim (verbatimCat e c) s))
        | _ => rs := (acc.push ·) <$> (← resolve (some g) (childNs g ns) child)
    tried := tried.push (c, rs)
  let segments := tried.map fun (c, rs) => (c, rs.toOption.bind (segmentsFor e c))
  let ok := segments.toList.filterMap fun (c, segs) => segs.map fun _ => c
  let fits (c : Web.Cat) := parent.all fun g => g.letters.any (Web.vocab.widens c)
  let chosen ← match parent with
    | none =>
      match ok with
      | [c] => pure (some c)
      | [] => pure none
      | cs => return .error ⟨nameStx, s!"<{name}> could take any of \
          {", ".intercalate (cs.map catName)} here; give the expected type, such as \
          (html! … : Html.Node .flow)"⟩
    | some _ =>
      let fitting := ok.filter fits
      pure ((least? fitting).orElse fun _ => fitting.head? |>.orElse fun _ =>
        (least? ok).orElse fun _ => ok.head?)
  match chosen with
  | some c =>
    match segments.find? (·.1 == c) with
    | some (_, some rs) => return .ok (.elem e c payload rs name)
    | _ => return .error ⟨nameStx, s!"<{name}>: no category"⟩
  | none =>
    -- Report against the category the element would most plausibly take.
    let preferred := (cats.find? fits).orElse fun _ => cats.head?
    match preferred.bind fun c => tried.find? (·.1 == c) with
    | some (_, .error err) => return .error err
    | some (c, .ok rs) => return .error (rejectionErr name nameStx e c children rs)
    | none => return .error ⟨stx, s!"<{name}> takes no category"⟩

end

/-! ### Elaborating attributes and children -/

def nameOf (stx : Syntax) : String :=
  match stx with
  | .node _ _ #[.atom _ v] => v
  | .atom _ v => v
  | _ => stx.getAtomVal

/-- Boolean attributes, as written, and their HTML names. -/
def boolAttrs : List (String × String) :=
  [("checked", "checked"), ("selected", "selected"), ("disabled", "disabled"), ("hidden", "hidden"),
   ("readonly", "readonly"), ("readOnly", "readonly"), ("required", "required"),
   ("multiple", "multiple"), ("autofocus", "autofocus"), ("open", "open"), ("muted", "muted"),
   ("controls", "controls"), ("autoplay", "autoplay"), ("loop", "loop"),
   ("novalidate", "novalidate")]

def isEventName (n : String) : Bool :=
  n.length > 2 && n.startsWith "on" && (n.toList[2]?.map Char.isUpper).getD false

def renamed (name : String) : String :=
  if name == "className" then "class" else if name == "htmlFor" then "for" else name

/-- Elaborates `t`, giving it a chance to be postponed until its type is known. -/
def elabTyped (t : Syntax) : TermElabM (Expr × Expr) := do
  let e ← elabTerm t none
  synthesizeSyntheticMVars (postpone := .yes)
  let ty ← whnfR (← instantiateMVars (← inferType e))
  if !ty.getAppFn.isMVar then return (e, ty)
  tryPostpone
  synthesizeSyntheticMVars (postpone := .partial)
  return (e, ← whnfR (← instantiateMVars (← inferType e)))

/-- `e` reduced to constructors, as the categories in a type are. -/
def normalize (fuel : Nat) (e : Expr) : MetaM Expr := do
  match fuel with
  | 0 => return e
  | fuel + 1 =>
    let e ← whnf e
    return mkAppN e.getAppFn (← e.getAppArgs.mapM (normalize fuel))

def catsByExpr : Std.HashMap Expr Web.Cat :=
  Web.Cat.all.foldl (fun m c => m.insert (toExpr c) c) {}

def decodeCat? (c : Expr) : MetaM (Option Web.Cat) := do
  let c ← instantiateMVars c
  if c.hasMVar then return none
  return catsByExpr[← normalize 4 c]?

/-- The payload and category of a node type, which `ty` is if it unfolds to `HtmlModel.Node`. -/
def nodeType? (ty : Expr) : MetaM (Option (Expr × Expr)) := do
  match (← whnfR (← instantiateMVars ty)).getAppFnArgs with
  | (``HtmlModel.Node, #[S, P, c]) =>
    unless ← isDefEq S sigExpr do return none
    return some (P, c)
  | _ => return none

def spliceTypes : String :=
  "a child {…} must be a node (Web.Node P c), a List, Array or Option of nodes, a String or \
    a number"

def textChild (P s : Expr) (ref : Syntax) (what : String) : Child :=
  .seg (.one .text) (mkApp4 (mkConst ``Seg.one) sigExpr P (toExpr Web.Cat.text)
    (mkApp3 (mkConst ``HtmlModel.Node.text) sigExpr P s)) ref what

/-- The segment a child splice stands for, by its type. -/
def elabChildSplice (P : Expr) (t : Syntax) : TermElabM Child := withRef t do
  let (e, ty) ← elabTyped t
  let node (X : Expr) : TermElabM Web.Cat := do
    let X ← whnfR (← instantiateMVars X)
    if X.getAppFn.isMVar then
      discard <| isDefEq X (mkApp2 (mkConst ``Web.Node) P (← mkFreshExprMVar (mkConst ``Web.Cat)))
    let some (P', c) ← nodeType? X |
      throwError "html!: this has type{indentExpr ty}\n{spliceTypes}"
    unless ← isDefEq P' P do
      throwError "html!: this node's payload is{indentExpr P'}\nbut the element's is{indentExpr P}"
    let some cat ← decodeCat? c |
      throwError "html!: the category of this child is not known at compile time; give its type, \
        such as ([] : List (Html.Node .flow))"
    return cat
  let seg (k : Kind) (s : Expr) (what : String) := Child.seg k s t what
  match ty.getAppFnArgs with
  | (``List, #[X]) =>
    let c ← node X
    return seg (.many c) (mkApp4 (mkConst ``Seg.ofList) sigExpr P (toExpr c) e)
      s!"a list of {catName c}"
  | (``Array, #[X]) =>
    let c ← node X
    let l := mkApp2 (mkConst ``Array.toList [0]) X e
    return seg (.many c) (mkApp4 (mkConst ``Seg.ofList) sigExpr P (toExpr c) l)
      s!"an array of {catName c}"
  | (``Option, #[X]) =>
    let c ← node X
    return seg (.opt c) (mkApp4 (mkConst ``Seg.ofOption) sigExpr P (toExpr c) e)
      s!"an optional {catName c}"
  | (``String, #[]) => return textChild P e t "text"
  | (``Nat, #[]) | (``Int, #[]) | (``Float, #[]) | (``Char, #[]) =>
    return textChild P (← mkAppM ``ToString.toString #[e]) t "text"
  | _ =>
    if (← nodeType? ty).isSome then
      let c ← node ty
      return seg (.one c) (mkApp4 (mkConst ``Seg.one) sigExpr P (toExpr c) e)
        s!"a node of {catName c}"
    throwError "html!: this has type{indentExpr ty}\n{spliceTypes}"

/-- Inter-element whitespace, which may stand where text may not. -/
def wsChild (P : Expr) (ref : Syntax) : MetaM Child := do
  let s := mkStrLit " "
  let h ← mkDecideProof
    (← mkEq (mkApp (mkConst ``HtmlModel.isWhitespace) s) (mkConst ``Bool.true))
  let h := mkConst (← mkAuxLemma [] (← inferType h) h)
  let n := mkApp3 (mkConst ``Web.ws) P s h
  return .seg (.one .ws) (mkApp4 (mkConst ``Seg.one) sigExpr P (toExpr Web.Cat.ws) n) ref
    "whitespace"

/-- An event attribute, elaborated once its payload type is known, so that a payload without
event support is reported as such. -/
syntax (name := eventTerm) "html_event% " str term:max term:max : term

@[term_elab eventTerm] def elabEvent : TermElab := fun stx _ => do
  let name := stx[1].isStrLit?.getD ""
  let p ← elabTerm stx[3] none
  let P ← instantiateMVars (← inferType p)
  if P.getAppFn.isMVar then tryPostpone
  let α ← mkFreshTypeMVar
  let cls := mkApp3 (mkConst ``EventAttr) P (mkStrLit name) α
  let inst ← if P.getAppFn.isMVar then mkInstMVar cls else
    match ← synthInstance? cls with
    | some inst =>
      discard <| isDefEq (← inferType inst) cls
      pure inst
    | none => throwError "html!: the payload{indentExpr P}\nhas no event support: there is no \
        instance of EventAttr {P} \"{name}\" _"
  let v ← elabTermEnsuringType stx[2] (← instantiateMVars α)
  return mkApp6 (mkConst ``EventAttr.on) P (mkStrLit name) α inst v p

/-- What the attributes before one have built. -/
structure AttrState where
  payload : Expr
  /-- The child `textContent` or `innerHTML` stands for. -/
  child : Option Child := none
  keyed : Bool := false

def styleListType : MetaM Expr := do
  mkAppM ``List #[← mkAppM ``Prod #[mkConst ``String, mkConst ``String]]

def elabAttr (P inst : Expr) (st : AttrState) (a : Syntax) : TermElabM AttrState := withRef a do
  let op (n : Name) := mkApp2 (mkConst n) P inst
  let p := st.payload
  match a with
  | `(jsxAttr| { $t:term }) =>
    return { st with payload := mkApp2 (op ``HtmlPayload.append) p (← elabTermEnsuringType t P) }
  | `(jsxAttr| $n:jsxName) =>
    let name := nameOf n
    if name == "key" || isEventName name || name == "textContent" || name == "innerHTML" then
      throwError "{name} needs a value: {name}=\{…}"
    let name := renamed ((boolAttrs.lookup name).getD name)
    return { st with
      payload := mkApp3 (op ``HtmlPayload.flag) (mkStrLit name) (mkConst ``Bool.true) p }
  | `(jsxAttr| $n:jsxName = $v:jsxAttrVal) =>
    let name := nameOf n
    let value : Sum String Syntax := match v.raw[0] with
      | s@(.node _ `str _) => .inl (s.isStrLit?.getD "")
      | .node _ _ #[_, t, _] => .inr t
      | _ => .inl ""
    let valueStr : TermElabM Expr := match value with
      | .inl s => pure (mkStrLit s)
      | .inr t => withRef t do
        elabTermEnsuringType (← `(HtmlSyntax.ToAttrValue.toAttrValue $(⟨t⟩)))
          (mkConst ``String)
    let set (payload : Expr) : TermElabM AttrState := return { st with payload }
    if name == "key" then
      if st.keyed then throwError "the element already has a key"
      return { st with payload := mkApp2 (op ``HtmlPayload.key) (← valueStr) p, keyed := true }
    else if name == "textContent" || name == "innerHTML" then
      if st.child.isSome then throwError "the element already has textContent or innerHTML"
      let s ← match value with
        | .inl s => pure (mkStrLit s)
        | .inr t => elabTermEnsuringType t (mkConst ``String)
      let child := if name == "innerHTML" then .verbatim s a else textChild P s a "textContent"
      return { st with child := some child }
    else if name.startsWith "on" && name.length > 2 && !isEventName name then
      throwErrorAt n "event attributes are written in camel case: \
        on{(name.drop 2).toString.capitalize}=\{…}"
    else if isEventName name then
      let .inr t := value | throwError "{name} takes a Lean value: {name}=\{…}"
      let p ← exprToSyntax p
      set (← elabTerm (← `(html_event% $(quote name) $(⟨t⟩) $p)) (some P))
    else if let some flagName := boolAttrs.lookup name then
      let .inr t := value | throwError
        "{name} is a boolean attribute: write {name}=\{true}, {name}=\{b} or a bare {name}"
      let b ← elabTermEnsuringType t (mkConst ``Bool)
      set (mkApp3 (op ``HtmlPayload.flag) (mkStrLit flagName) b p)
    else
      let name := renamed name
      match name, value with
      | "style", .inr t =>
        let (e, ty) ← withRef t (elabTyped t)
        if ty.isConstOf ``String then set (mkApp3 (op ``HtmlPayload.attr) (mkStrLit name) e p)
        else
          let l ← withRef t <| ensureHasType (← styleListType) e
          set (mkApp2 (mkApp2 (mkConst ``HtmlSyntax.styles) P inst) l p)
      | _, _ => set (mkApp3 (op ``HtmlPayload.attr) (mkStrLit name) (← valueStr) p)
  | _ => throwError "unsupported attribute"

/-- JSX spacing: whitespace on one line after a child, which the token before it consumed, is a
space; whitespace containing a line break is not. -/
def spaceAfter (stx : Syntax) : Bool :=
  match stx.getTailInfo with
  | .original _ _ trailing _ => let w := trailing.toString; !w.isEmpty && !w.contains '\n'
  | _ => false

mutual

/-- `fuel` bounds the nesting, as the number of syntax nodes does. -/
def elabElement (P inst : Expr) (fuel : Nat) (e : Syntax) : StateT Nat TermElabM Child := do
  let fuel + 1 := fuel | throwErrorAt e "html!: nested too deeply"
  let (nameStx, attrs, children, closing) ← match e with
    | `(jsxElement| < $n:jsxName $as:jsxAttr* />) => pure (n.raw, as.map (·.raw), #[], none)
    | `(jsxElement| < $n:jsxName $as:jsxAttr* > $cs:jsxChild* </ $m:jsxName >) =>
      pure (n.raw, as.map (·.raw), cs.map (·.raw), some m.raw)
    | _ => throwErrorAt e "expected an element"
  let tag := nameOf nameStx
  if let some m := closing then
    if nameOf m != tag then throwErrorAt m "</{nameOf m}> closes <{tag}>"
  let st ← attrs.foldlM (init := { payload := mkApp2 (mkConst ``HtmlPayload.empty) P inst })
    fun st a => elabAttr P inst st a
  let mut childs := #[]
  let mut prev : Syntax := e[3]
  for c in children do
    childs := childs ++ (← elabChild P inst fuel (spaceAfter prev) c)
    prev := c
  if (children.back?.map (·[0].getKind != ``childText)).getD false && spaceAfter prev then
    childs := childs.push (← wsChild P prev)
  if let some c := st.child then
    unless childs.isEmpty do
      throwErrorAt c.ref "textContent and innerHTML replace the element's children, so it can \
        have no others"
    childs := #[c]
  let id ← getModify (· + 1)
  return .elem id tag nameStx e st.payload childs

/-- One child, after a space on the same line if `lead`. -/
def elabChild (P inst : Expr) (fuel : Nat) (lead : Bool) (c : Syntax) :
    StateT Nat TermElabM (Array Child) := do
  let space : StateT Nat TermElabM (Array Child) :=
    if lead then return #[← wsChild P c] else return #[]
  let c := c[0]
  match c with
  | `(childText| $t:jsxText) =>
    let raw := (if lead then " " else "") ++ nameOf t
    -- Whitespace-only text spanning lines is layout, not content.
    if raw.all Char.isWhitespace && raw.contains '\n' then return #[]
    let s := decodeEntities (jsxWhitespace raw)
    if s.isEmpty then return #[]
    if isWhitespace s then return #[← wsChild P c]
    return #[textChild P (mkStrLit s) c "text"]
  | `(childTerm| { $t:term }) => return (← space).push (← elabChildSplice P t)
  | `(childElement| $e:jsxElement) => return (← space).push (← elabElement P inst fuel e)
  | _ => throwErrorAt c "unsupported child"

end

/-! ### Building the term -/

abbrev BuildM := StateT (Std.HashMap Expr Expr) MetaM

/-- A proof of `p` by `decide`, as an auxiliary lemma shared by every element that needs it. -/
def decided (p : Expr) : BuildM Expr := do
  if let some h := (← get)[p]? then return h
  let h ← mkDecideProof p
  let h := mkConst (← mkAuxLemma [] p h)
  modify (·.insert p h)
  return h

def elemExpr : Web.Elem → BuildM Expr
  | .html e => return mkApp (mkConst ``Web.Elem.html) (toExpr e)
  | .svg e => return mkApp (mkConst ``Web.Elem.svg) (toExpr e)
  | .mathml e => return mkApp (mkConst ``Web.Elem.mathml) (toExpr e)
  | .custom name _ => do
    let h ← decided
      (← mkEq (mkApp (mkConst ``isCustomElementName) (mkStrLit name)) (mkConst ``Bool.true))
    return mkApp2 (mkConst ``Web.Elem.custom) (mkStrLit name) h

def vocabExpr : Expr := mkConst ``Web.vocab

/-- A proof that `e` as `c` admits children of kinds `ks`. Where the content model takes its
children in any order, the proof is of the coarser `Shape.kinds`, since deciding a shape of many
children that might be whitespace, and so optional, is slow in the kernel. -/
def admitsProof (e : Web.Elem) (c : Web.Cat) (ks : List Kind) (eE cE ksE : Expr) : BuildM Expr := do
  if admitsKinds e c ks then
    let f := mkApp4 (mkConst ``Vocabulary.admits_of_kinds) vocabExpr eE cE ksE
    let .forallE _ dom _ _ ← whnf (← inferType f) |
      throwError "html!: unexpected admits_of_kinds"
    return mkApp f (← decided dom)
  decided (mkApp4 (mkConst ``Vocabulary.Admits) vocabExpr eE cE ksE)

/-- `xs` as a tree of `join`s over runs of at most 32, each made by `run`. Lean's compiler
recurses on a term as deeply as it nests, so that a long chain of `cons` would exceed its depth. -/
def balanced {α β : Type} (xs : Array α) (run : Array α → β) (join : β → β → β) :
    β :=
  if h : xs.size ≤ 32 then run xs else
    let mid := xs.size / 2
    join (balanced (xs.extract 0 mid) run join) (balanced (xs.extract mid xs.size) run join)
termination_by xs.size
decreasing_by all_goals simp only [Array.size_extract]; omega

def listExpr (ty : Expr) (xs : Array Expr) : Expr :=
  balanced xs (·.foldr (mkApp3 (mkConst ``List.cons [0]) ty) (mkApp (mkConst ``List.nil [0]) ty))
    (mkApp3 (mkConst ``List.append [0]) ty)

/-- The kinds of a run of segments, and the segments, of type `Segs` of those kinds. -/
def segsExpr (P : Expr) (xs : Array (Expr × Expr)) : Expr × Expr :=
  let kindTy := mkApp (mkConst ``SegK) (mkConst ``Web.Cat)
  balanced xs
    (·.foldr
      (init := (mkApp (mkConst ``List.nil [0]) kindTy, mkApp2 (mkConst ``Segs.nil) sigExpr P))
      fun (k, x) (ks, segs) => (mkApp3 (mkConst ``List.cons [0]) kindTy k ks,
        mkApp6 (mkConst ``Segs.cons) sigExpr P k ks x segs))
    fun (ks, xs) (ls, ys) =>
      (mkApp3 (mkConst ``List.append [0]) kindTy ks ls,
        mkApp6 (mkConst ``Segs.append) sigExpr P ks ls xs ys)

/-- A child's segment, and its node if it is an element. -/
def build (P : Expr) : RChild → BuildM (Expr × Option Expr)
  | .seg _ s _ => return (s, none)
  | .verbatim c s =>
    return (mkApp4 (mkConst ``Seg.one) sigExpr P (toExpr c)
      (mkApp4 (mkConst ``HtmlModel.Node.verbatim) sigExpr P (toExpr c) s), none)
  | .group c members => do
    let nodes ← members.attach.filterMapM fun ⟨m, _⟩ => return (← build P m).2
    let l := listExpr (mkApp2 (mkConst ``Web.Node) P (toExpr c)) nodes
    return (mkApp4 (mkConst ``Seg.ofList) sigExpr P (toExpr c) l, none)
  | .elem e c payload children _ => do
    let built ← children.attach.mapM fun ⟨child, _⟩ =>
      return (child.kind.toExpr, (← build P child).1)
    let (ks, segs) := segsExpr P built
    let eE ← elemExpr e
    let cE := toExpr c
    let hc ← decided (mkApp2 (mkConst ``HtmlSyntax.Takes) eE cE)
    let ok ← admitsProof e c (children.toList.map (·.kind)) eE cE ks
    let n := mkAppN (mkConst ``Web.elem) #[P, eE, cE, payload, ks, segs, hc, ok]
    return (mkApp4 (mkConst ``Seg.one) sigExpr P cE n, some n)

/-! ### `html!` -/

def expectedNode (expected? : Option Expr) : TermElabM (Expr × Option Web.Cat) := do
  let fresh := return (← mkFreshTypeMVar, none)
  let some ty := expected? | fresh
  let some (P, c) ← nodeType? ty | fresh
  return (P, ← decodeCat? c)

@[term_elab htmlTerm] def elabHtml : TermElab := fun stx expected? => do
  let (P, d?) ← expectedNode expected?
  let inst ← mkInstMVar (mkApp (mkConst ``HtmlPayload) P)
  let mut size := 0
  for _ in stx[1].topDown do size := size + 1
  let root ← (elabElement P inst size stx[1]).run' 0
  -- The namespace the expected category belongs to, or any where there is none.
  let ns : Option Namespace := match d? with
    | some (.html _) => some .html
    | some (.svg _) => some .svg
    | some (.mathml _) => some .mathml
    | _ => none
  let (r, _) := (resolve (d?.map .sym) ns root).run {}
  let r ← match r with
    | .ok r => pure r
    | .error err => throwErrorAt err.ref err.msg
  let .elem _ c _ _ name := r | throwError "html!: expected an element"
  let ((_, some n), cache) ← (build P r).run {} | throwError "html!: expected an element"
  match d?, expected? with
  | some d, some ty =>
    -- The type as the caller wrote it, such as `Html.Node .flow`, so that dot notation finds
    -- its namespace.
    let ty ← instantiateMVars ty
    if c == d then mkExpectedTypeHint n ty else
    unless Web.vocab.widens c d do
      throwErrorAt stx[1][1] "<{name}> as {catName c} cannot stand where {catName d} is expected"
    let widens := mkApp3 (mkConst ``Vocabulary.widens) vocabExpr (toExpr c) (toExpr d)
    let h ← (decided (← mkEq widens (mkConst ``Bool.true))).run' cache
    mkExpectedTypeHint (mkApp5 (mkConst ``Web.widen) P (toExpr c) (toExpr d) n h) ty
  | _, _ => return n

end

end HtmlSyntax
