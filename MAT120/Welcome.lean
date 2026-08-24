import Verbose.French.ExampleLib

open Verbose.French

example (P Q : Prop) (hP : P) (hPQ : P → Q) : Q := by
  with_suggestions
    exact hPQ hP
