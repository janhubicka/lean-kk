import Kk.HensonAlgorithmRunAllGenerationCapacity
import SuccessorTree.V10.PrescribedCorrectedB3
import Mathlib.Tactic

/-!
# The precise L-reduct profile sufficient for transfer of corrected B3

The corrected boring-extension age test is a predicate on finite L-only
continuation witnesses. Even though its prescribed partial-type inputs
contain the full auxiliary E data, the age-test witnesses themselves
have no E: they only see the complete ordinary L-socle at the cut and
the SET of allowed complete upper L-reduct types.

Consequently one can transfer B3 from a smaller *marked* profile to a
larger *full* profile provided that (a) each full source socle has a
corresponding marked ordinary L-socle and (b) each allowed full upper
L-type is also allowed by the marked source. This does NOT need
equality of L+ source types, E bits, or individual original names.

This is a **conditional transfer theorem**. In the specially resolved
K_k-free diary, the difficult, still-open geometrical task is to prove
the two reduct-profile conditions for complete parameter-closed
auxiliary gadgets. In particular, finite H original nonedges alone
do not imply the required upper-type dominance for arbitrary age
continuations, whose upper-upper L-edges are freely variable.
-/

namespace Kk

open SuccessorTree.V10

/-- Corrected B3 depends monotonically on the L-only age profile.

The "full" source need not be a subset of "marked" as L+ records.
For every full source socle it suffices to find one marked source
with the same *ordinary L-socle*, and the allowed full upper
L-reducts must be included in the allowed marked upper L-reducts.

The conclusion is only B3 admissibility, not existence of a common
envelope or of a global shape map. -/
theorem correctedB3_of_Lprofile_dominance
    {cut db du dd : Nat}
    (full marked : PrescribedBoringData cut db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hSocle : ∀ S, S ∈ full.source →
      ∃ T, T ∈ marked.source ∧
        SameInitialL
          (prescribedOrdinarySocle (full.target S))
          (prescribedOrdinarySocle (marked.target T)) cut)
    (hUpper : ∀ R, full.PrescribedUpperLType R →
      marked.PrescribedUpperLType R)
    (hMarked : marked.CorrectedB3 family) :
    full.CorrectedB3 family := by
  intro S hS W hFinite hSame hUpperW hDelete
  obtain ⟨T,hT,hSameSocle⟩ := hSocle S hS
  have hWMarked :
      SameInitialL W
        (prescribedOrdinarySocle (marked.target T)) cut :=
    hSame.trans hSameSocle
  have hUpperMarked :
      UpperTypesPrescribed W cut marked.PrescribedUpperLType := by
    intro x hx hAbove
    exact hUpper _ (hUpperW x hx hAbove)
  exact hMarked T hT W hFinite hWMarked hUpperMarked hDelete

/-- A full (B3) failure remains visible to the marked B3 test
whenever the two explicit L-profile dominance conditions hold.
This contrapositive does not assert they hold in the resolved copy. -/
theorem failed_markedB3_of_Lprofile_dominance
    {cut db du dd : Nat}
    (full marked : PrescribedBoringData cut db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hSocle : ∀ S, S ∈ full.source →
      ∃ T, T ∈ marked.source ∧
        SameInitialL
          (prescribedOrdinarySocle (full.target S))
          (prescribedOrdinarySocle (marked.target T)) cut)
    (hUpper : ∀ R, full.PrescribedUpperLType R →
      marked.PrescribedUpperLType R)
    (hFailure : ¬ full.CorrectedB3 family) :
    ¬ marked.CorrectedB3 family := by
  intro hMarked
  exact hFailure
    (correctedB3_of_Lprofile_dominance
      full marked family hSocle hUpper hMarked)

/-- Mutual dominance of the **ordinary L-only** age profiles is
enough for equivalence of the full corrected B3 tests. No equality
of auxiliary E data or of labelled envelope carriers is inferred. -/
theorem correctedB3_iff_of_equal_Lprofiles
    {cut db du dd : Nat}
    (F G : PrescribedBoringData cut db du dd)
    (family : List (NormalizedForbidden db du dd))
    (hFGSocle : ∀ S, S ∈ F.source →
      ∃ T, T ∈ G.source ∧
        SameInitialL
          (prescribedOrdinarySocle (F.target S))
          (prescribedOrdinarySocle (G.target T)) cut)
    (hFGUpper : ∀ R, F.PrescribedUpperLType R →
      G.PrescribedUpperLType R)
    (hGFSocle : ∀ T, T ∈ G.source →
      ∃ S, S ∈ F.source ∧
        SameInitialL
          (prescribedOrdinarySocle (G.target T))
          (prescribedOrdinarySocle (F.target S)) cut)
    (hGFUpper : ∀ R, G.PrescribedUpperLType R →
      F.PrescribedUpperLType R) :
    F.CorrectedB3 family ↔ G.CorrectedB3 family := by
  constructor
  · intro hF
    exact correctedB3_of_Lprofile_dominance
      G F family hGFSocle hGFUpper hF
  · intro hG
    exact correctedB3_of_Lprofile_dominance
      F G family hFGSocle hFGUpper hG

end Kk
