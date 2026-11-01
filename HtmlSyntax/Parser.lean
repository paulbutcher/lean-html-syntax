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

public import Lean.Parser
public meta import Lean.Parser

public section

namespace HtmlSyntax

open Lean Parser

/-- Characters that end JSX text. -/
meta def textStop (c : Char) : Bool := c == '<' || c == '>' || c == '{' || c == '}' || c == '$'

/-- Plain text between tags. -/
meta def jsxText : Parser :=
  withAntiquot (mkAntiquot "jsxText" `HtmlSyntax.jsxText) {
    fn := fun c s =>
      let startPos := s.pos
      let s := takeWhile1Fn (fun c => !textStop c) "text" c s
      mkNodeToken `HtmlSyntax.jsxText startPos true c s }

meta def nameChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == ':' || c == '.'

/-- A tag or attribute name: letters, digits, `-`, `_`, `:` and `.`. -/
meta def jsxName : Parser :=
  withAntiquot (mkAntiquot "jsxName" `HtmlSyntax.jsxName) {
    fn := fun c s =>
      let startPos := s.pos
      if c.atEnd startPos then s.mkEOIError
      else
        let ch := c.get startPos
        if !(ch.isAlpha || ch == '_') then s.mkUnexpectedError "expected a tag or attribute name"
        else
          let s := takeWhileFn nameChar c (s.next c startPos)
          mkNodeToken `HtmlSyntax.jsxName startPos true c s }

@[combinator_formatter jsxText] meta def jsxText.formatter : PrettyPrinter.Formatter := pure ()
@[combinator_parenthesizer jsxText] meta def jsxText.parenthesizer : PrettyPrinter.Parenthesizer :=
  pure ()
@[combinator_formatter jsxName] meta def jsxName.formatter : PrettyPrinter.Formatter := pure ()
@[combinator_parenthesizer jsxName] meta def jsxName.parenthesizer : PrettyPrinter.Parenthesizer :=
  pure ()

declare_syntax_cat jsxElement
declare_syntax_cat jsxAttr

syntax jsxAttrVal := str <|> group("{" term "}")
syntax (name := attrValue) jsxName "=" jsxAttrVal : jsxAttr
syntax (name := attrSplice) "{" term "}" : jsxAttr
syntax (name := attrFlag) jsxName : jsxAttr

syntax (name := selfClosing) "<" jsxName jsxAttr* "/>" : jsxElement

-- Children are ordered alternatives, not a syntax category: a category first
-- reads a token, and text may start with a character no token starts with.
syntax childText := jsxText
syntax childTerm := "{" term "}"
syntax childElement := jsxElement
syntax jsxChild := childText <|> childTerm <|> childElement
syntax (name := withChildren) "<" jsxName jsxAttr* ">" jsxChild* "</" jsxName ">" : jsxElement

/-- JSX-like markup for lean-html-model nodes, each element's children checked against its
content model while Lean elaborates. -/
syntax (name := htmlTerm) "html!" jsxElement : term

end HtmlSyntax
