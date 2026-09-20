import Bugeaud105.Main
import FormalConjectures.Books.BugeaudDistributionModuloOne.Problem10_5

/-!
# Exact compatibility with the pinned Formal Conjectures statements

The original conjectures are used only to obtain their types.  Their placeholder
proofs are never used.  The limsup statement follows through the existing proved
implication, supplied with the independently constructed moreover proof.
-/

namespace Bugeaud105

theorem problem_10_5_moreover : type_of% Bugeaud05.problem_10_5_moreover := by
  intro K _ ε hε
  exact moreover K hε

theorem problem_10_5 : type_of% Bugeaud05.problem_10_5 :=
  Bugeaud05.problem_10_5_of_moreover problem_10_5_moreover

end Bugeaud105
