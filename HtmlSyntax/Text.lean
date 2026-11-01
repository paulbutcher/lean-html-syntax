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

@[expose] public section

namespace HtmlSyntax

/-- JSX whitespace: lines are trimmed, blank lines dropped, the rest joined with spaces; runs of
spaces inside a line become one. -/
def jsxWhitespace (s : String) : String :=
  let lines := s.splitOn "\n"
  let multi := lines.length > 1
  let lines := lines.mapIdx fun i l =>
    let l := if multi && i > 0 then l.trimAsciiStart.toString else l
    let l := if multi && i + 1 < lines.length then l.trimAsciiEnd.toString else l
    l
  let lines := if multi then lines.filter (!·.isEmpty) else lines
  let joined := " ".intercalate lines
  let (out, _) := joined.foldl (init := ("", false)) fun (out, sp) c =>
    if c.isWhitespace then (if sp then (out, true) else (out.push ' ', true))
    else (out.push c, false)
  out

def hexValue? (s : String) : Option Nat :=
  s.foldl (fun acc c => acc.bind fun v =>
    if c.isDigit then some (v * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c.toLower ∧ c.toLower ≤ 'f' then
      some (v * 16 + (c.toLower.toNat - 'a'.toNat + 10))
    else none) (some 0)

/-- The text an entity's name, between `&` and `;`, stands for. -/
def decodeEntity? : String → Option String
  | "amp" => some "&" | "lt" => some "<" | "gt" => some ">" | "quot" => some "\""
  | "apos" => some "'" | "nbsp" => some " " | "copy" => some "©" | "mdash" => some "—"
  | "ndash" => some "–" | "hellip" => some "…" | "times" => some "×" | "rarr" => some "→"
  | "larr" => some "←"
  | n =>
    if n.startsWith "#x" || n.startsWith "#X" then
      (hexValue? (n.drop 2).toString).map fun v => (Char.ofNat v).toString
    else if n.startsWith "#" then ((n.drop 1).toString.toNat?).map fun v => (Char.ofNat v).toString
    else none

/-- Decodes `&amp;`, `&lt;`, `&gt;`, `&quot;`, `&apos;`, `&nbsp;`, `&#N;` and `&#xH;` in text, as
JSX does, leaving any other `&` as it stands. -/
def decodeEntities (s : String) : String :=
  match s.splitOn "&" with
  | [] => s
  | first :: parts => parts.foldl (init := first) fun out p =>
    match p.splitOn ";" with
    | name :: rest@(_ :: _) =>
      match decodeEntity? name with
      | some d => out ++ d ++ ";".intercalate rest
      | none => out ++ "&" ++ p
    | _ => out ++ "&" ++ p

end HtmlSyntax
