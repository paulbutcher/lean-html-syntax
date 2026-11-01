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

public import Html

@[expose] public section

namespace HtmlSyntax

/-- What `html!` builds an element's payload with. Each attribute is applied in the order written,
to the payload built from those before it, so that an instance can make the last occurrence of a
name win. -/
class HtmlPayload (P : Type) where
  empty : P
  attr : String → String → P → P
  /-- A boolean attribute: present when `true`, absent when `false`. -/
  flag : String → Bool → P → P
  /-- One inline style property, from `style={[(name, value), …]}`. -/
  style : String → String → P → P
  /-- The element's identity among its siblings, for a renderer that diffs. -/
  key : String → P → P
  /-- An attribute splice `{p}`, whose attributes override those before it. -/
  append : P → P → P

/-- An event attribute, such as `onClick`, on payload `P`. `event` is the attribute's name as
written, so that an instance can give `onEnter` a meaning no DOM event has. -/
class EventAttr (P : Type) (event : String) (α : outParam Type) where
  on : α → P → P

/-- Attribute values given as `{term}`. -/
class ToAttrValue (α : Type) where
  toAttrValue : α → String

instance : ToAttrValue String := ⟨id⟩
instance : ToAttrValue Nat := ⟨toString⟩
instance : ToAttrValue Int := ⟨toString⟩
instance : ToAttrValue Float := ⟨toString⟩

/-- Inline styles from `style={[("color", "red")]}`. -/
def styles {P : Type} [HtmlPayload P] (l : List (String × String)) (p : P) : P :=
  l.foldl (fun p (n, v) => HtmlPayload.style n v p) p

namespace Attrs

open Html

/-- What makes two names the same attribute, as `Attrs.render` compares them. -/
def nameKey (name : String) : String := attrNameKey (sanitizeAttrName name)

/-- `f` in place of the fragment of the same name, or after the others if there is none. -/
def set (attrs : Attrs) (f : AttrFragment) : Attrs :=
  let k := nameKey f.name
  if attrs.any (nameKey ·.name == k) then attrs.map fun g => if nameKey g.name == k then f else g
  else attrs ++ [f]

def remove (attrs : Attrs) (name : String) : Attrs :=
  attrs.filter (nameKey ·.name != nameKey name)

def addStyle (attrs : Attrs) (name value : String) : Attrs :=
  let decl := s!"{name}:{value}"
  match attrs.find? (nameKey ·.name == "style") with
  | some (.value _ s) => set attrs (.value "style" (if s.isEmpty then decl else s ++ ";" ++ decl))
  | _ => set attrs (.value "style" decl)

end Attrs

/-- lean-html renders the first occurrence of a repeated name, so each attribute replaces any of
the same name, keeping its position, to make the last written win. -/
instance : HtmlPayload Html.Attrs where
  empty := []
  attr n v a := Attrs.set a (.value n v)
  flag n b a := if b then Attrs.set a (.flag n) else Attrs.remove a n
  style n v a := Attrs.addStyle a n v
  key _ a := a
  append a b := b.foldl Attrs.set a

end HtmlSyntax
