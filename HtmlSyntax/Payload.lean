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

public import HtmlModel

@[expose] public section

namespace HtmlSyntax

/-- Attribute values given as `{term}`. -/
class ToAttrValue (α : Type) where
  toAttrValue : α → String

instance : ToAttrValue String := ⟨id⟩
instance : ToAttrValue Nat := ⟨toString⟩
instance : ToAttrValue Int := ⟨toString⟩
instance : ToAttrValue Float := ⟨toString⟩

/-- Inline styles from `style={[("color", "red")]}`. -/
def styles {P : Type} [HtmlModel.HtmlPayload P] (l : List (String × String)) (p : P) : P :=
  l.foldl (fun p (n, v) => HtmlModel.HtmlPayload.style n v p) p

end HtmlSyntax
