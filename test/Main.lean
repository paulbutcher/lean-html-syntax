/-
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import HtmlSyntaxTests

/-! Times elaborating generated views: a page of 2,001 elements in one `html!` term, and a view
whose parents hold a thousand literal children each, in content models that fix their order.

Each time excludes loading the imports and is budgeted in units of a fixed kernel reduction timed in
the same run, so that the budgets hold on a slower machine. -/

def header : String := "import HtmlSyntax\n\nopen Html\n\n"

def calibration : String :=
  header ++ "theorem calibration : (List.range 20000).foldl (· + ·) 0 = 199990000 := by decide +kernel\n"

/-- Twenty elements, the mix of an ordinary page. -/
def section_ (i : Nat) : String := s!"  <section>
    <p>Section {i} <span>x</span> <a href=\"/\">link</a></p>
    <ul><li><p>item 0</p></li><li><p>item 1</p></li><li><p>item 2</p></li><script></script></ul>
    <table><tbody><tr><td>a</td> <td>b</td></tr><tr><td>a</td> <td>b</td></tr></tbody></table>
  </section>\n"

def page : String :=
  header ++ "def page : Html.Node .flow := html! <div>\n" ++
    String.join ((List.range 100).map section_) ++ "</div>\n"

def wide : String :=
  header ++ "def wide : Html.Node .flow := html! <div>\n  <details><summary>s</summary>\n" ++
    String.join (List.replicate 1000 "    <div>x</div>\n") ++ "  </details>\n  <table>\n" ++
    String.join (List.replicate 1000 "    <tr><td>x</td></tr>\n") ++ "  </table>\n</div>\n"

/-- Milliseconds to elaborate `source`, or `none` if it fails. -/
def elaborate (name : String) (source : String) : IO (Option Nat) := do
  let dir : System.FilePath := ".lake" / "bench"
  IO.FS.createDirAll dir
  let path := dir / s!"{name}.lean"
  IO.FS.writeFile path source
  let start ← IO.monoMsNow
  let out ← IO.Process.output { cmd := "lake", args := #["env", "lean", path.toString] }
  let ms := (← IO.monoMsNow) - start
  if out.exitCode != 0 then
    IO.eprintln s!"{name}: failed to elaborate\n{out.stdout}{out.stderr}"
    return none
  return some ms

/-- The fastest of three runs, because noise in the baselines would scale every budget. -/
def fastest (name : String) (source : String) : IO (Option Nat) := do
  let runs ← (List.range 3).mapM fun _ => elaborate name source
  return (runs.mapM id).bind List.min?

def run (imports unit : Nat) (name : String) (budget : Nat) (source : String) : IO Bool := do
  let some total ← elaborate name source | return false
  let ms := total - imports
  let tenths := ms * 10 / unit
  IO.println s!"{name}: {ms} ms, {tenths / 10}.{tenths % 10} units"
  if ms > budget * unit then
    IO.eprintln s!"{name}: over the budget of {budget} units"
    return false
  return true

def main : IO UInt32 := do
  let some imports ← fastest "Imports" header | return 1
  let some calibrated ← fastest "Calibration" calibration | return 1
  let unit := max 1 (calibrated - imports)
  IO.println s!"Unit: {unit} ms"
  let page ← run imports unit "Page" 4 page
  let wide ← run imports unit "Wide" 4 wide
  return if page && wide then 0 else 1
