/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import HtmlSyntax
public import HtmlRenderer
meta import HtmlSyntax
meta import HtmlRenderer

/-! A payload with event support, as a downstream library would give one, and the rules of
lean-html-renderer's. -/

@[expose] public section

namespace HtmlSyntaxTests

open Html HtmlSyntax HtmlModel

inductive Msg where
  | inc
  | set (s : String)
  | pick (n : Nat)

/-- What `html!` asked of the payload. -/
structure Recorded where
  key : Option String := none
  attrs : List (String × String) := []
  events : List String := []
  input : Option (String → Msg) := none

instance : HtmlPayload Recorded where
  empty := {}
  attr n v p := { p with attrs := p.attrs ++ [(n, v)] }
  flag n b p := if b then { p with attrs := p.attrs ++ [(n, "")] } else p
  style n v p := { p with attrs := p.attrs ++ [("style:" ++ n, v)] }
  key k p := { p with key := some k }
  append p q := { p with attrs := p.attrs ++ q.attrs, events := p.events ++ q.events }

instance : EventAttr Recorded "onClick" Msg := ⟨fun _ p => { p with events := p.events ++ ["onClick"] }⟩
instance : EventAttr Recorded "onInput" (String → Msg) := ⟨fun f p => { p with input := some f }⟩

/-- The tree at `path`, each step the index of a child. -/
def treeAt {α : Type} : Web.Tree α → List Nat → Option (Web.Tree α)
  | t, [] => some t
  | .elem _ _ _ ch, i :: is | .unchecked _ _ _ _ ch, i :: is => ch[i]?.bind (treeAt · is)
  | _, _ :: _ => none

def payloadOf {c : Web.Cat} (n : Web.Node Recorded c) (path : List Nat) : Recorded :=
  match treeAt n.erase path with
  | some (.elem _ _ p _) => p
  | _ => {}

def childTags {α : Type} {c : Web.Cat} (n : Web.Node α c) (path : List Nat := []) :
    List (Namespace × String) :=
  match treeAt n.erase path with
  | some (.elem _ _ _ ch) | some (.unchecked _ _ _ _ ch) => ch.filterMap (·.tag)
  | _ => []

end HtmlSyntaxTests
