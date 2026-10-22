import Kk.OrderedSourceIdentification

/-!
# Common source top and code lengths determine all labelled prefixes

A stronger-looking common-source comparison can be replaced by simpler
concrete data: one genuine source TOP code and the selected source
length for each label. There is only one prefix of a given finite
table at a fixed length.

This is an alternative interface for the remaining resolved-diary
comparison. Instead of directly equating two sets of source vertices,
it can suffice to compare their common compressed top type and the
interesting/coding source levels. It is NOT asserted here that the
diary's macro-events determine those data.
-/

namespace Kk

open SuccessorTree.V10

universe u

variable {db du dd : Nat}
variable {family : List (NormalizedForbidden db du dd)}
variable {Λ : Type u}

/-- Two genuine G+ vertices which prefix the same top code and have
equal lengths are IDENTICAL, including every directed L+ and E bit. -/
theorem vertex_eq_of_common_top_and_size
    (top A B : FiniteGPlusVertex family)
    (hA : A.val.IsPrefix top.val)
    (hB : B.val.IsPrefix top.val)
    (hSize : A.val.size = B.val.size) : A = B := by
  apply Subtype.ext
  exact FinitePartialCode.prefix_unique_at_size hA hB hSize

/-- Labelled prefix chains are completely determined by one actual
top code and the length assigned to each label. No reference to
unlabelled ranges or canonical enumeration order is needed. -/
theorem labelled_prefix_chains_eq_of_common_top_and_sizes
    (top : FiniteGPlusVertex family)
    (P Q : Λ → FiniteGPlusVertex family)
    (hP : ∀ a, (P a).val.IsPrefix top.val)
    (hQ : ∀ a, (Q a).val.IsPrefix top.val)
    (hSize : ∀ a, (P a).val.size = (Q a).val.size) : P = Q := by
  funext a
  exact vertex_eq_of_common_top_and_size top
    (P a) (Q a) (hP a) (hQ a) (hSize a)

/-- The application-facing form under two GENUINE Kpt/G+ maps:
if the target vertices and target top are respectively images of
source tuples and the SAME source top, then equality of selected
source code lengths is sufficient to identify the common labelled
source. Prefix reflection supplies all source-prefix hypotheses.

This is potentially easier to verify from a resolved diary's
compressed interesting/coding level sequence than direct equality
of its selected-source inverse-image sets. -/
theorem labelled_sources_eq_of_common_top_and_cuts
    (F G : SuccessorTree.SMTree.MMap (normalizedKptSMTree family))
    (sourceTop : FiniteGPlusVertex family)
    (targetTopF targetTopG : FiniteGPlusVertex family)
    (targetF targetG : Λ → FiniteGPlusVertex family)
    (sourceF sourceG : Λ → FiniteGPlusVertex family)
    (hTopF : gPlusShapeImage F.map sourceTop = targetTopF)
    (hTopG : gPlusShapeImage G.map sourceTop = targetTopG)
    (hTargetF : ∀ a, gPlusShapeImage F.map (sourceF a) = targetF a)
    (hTargetG : ∀ a, gPlusShapeImage G.map (sourceG a) = targetG a)
    (hPrefF : ∀ a, (targetF a).val.IsPrefix targetTopF.val)
    (hPrefG : ∀ a, (targetG a).val.IsPrefix targetTopG.val)
    (hSizes : ∀ a, (sourceF a).val.size = (sourceG a).val.size) :
    sourceF = sourceG := by
  have hSourceF : ∀ a, (sourceF a).val.IsPrefix sourceTop.val := by
    intro a
    apply gPlusShapeImage_reflects_prefix F.map (sourceF a) sourceTop
    rw [hTargetF a, hTopF]
    exact hPrefF a
  have hSourceG : ∀ a, (sourceG a).val.IsPrefix sourceTop.val := by
    intro a
    apply gPlusShapeImage_reflects_prefix G.map (sourceG a) sourceTop
    rw [hTargetG a, hTopG]
    exact hPrefG a
  exact labelled_prefix_chains_eq_of_common_top_and_sizes
    sourceTop sourceF sourceG hSourceF hSourceG hSizes

end Kk
