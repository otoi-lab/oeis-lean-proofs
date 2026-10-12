import OeisProofs.FC.A8578
import OeisProofs.FC.A400194
import OeisProofs.FC.A384222

/-!
# Axiom audit

The four theorems linked from formal-conjectures depend only on the standard axioms.
The build fails if any other axiom (for example `sorryAx`) appears.
-/

/-- info: 'OeisA8578.conjecture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OeisA8578.conjecture

/-- info: 'OeisA400194.conjecture' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms OeisA400194.conjecture

/--
info: 'OeisA384222.conjecture_1' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OeisA384222.conjecture_1

/--
info: 'OeisA384222.conjecture_formula' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms OeisA384222.conjecture_formula
