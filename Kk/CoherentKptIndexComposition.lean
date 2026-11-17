import Kk.ConstructedPhysicalOldNewSourceIndex
import Mathlib.Tactic

/-!
# Track C: coherent Kpt index maps compose along physical root growth

English-first proof and adversarial scope audit:
  docs/track_c_coherent_index_composition_english_audit.md

This finite-index invariant transports ACTUAL Kpt nodes, so all
ordinary and auxiliary L+/E atoms are preserved on old names.
The live-mask transport is ONLY old-to-new and only below a
specified cutoff. New auxiliary nodes are allowed and expected.

No statement about the global resolved diary or common labelled
inverse monoid orbit is made.
-/

namespace Kk

open SuccessorTree
open SuccessorTree.V10

/-- An OLD-to-NEW coherent physical Kpt source-index map.
Its source and target indices are actual finite names for nodes
in the SAME normalized admissible Kpt successor tree.

The map is injective, preserves literal Kpt-node identity and
each live-cut bit in the forward direction up to the horizon.
No surjectivity or source-cardinality equality is required. -/
structure CoherentKptIndex
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {P Q : Nat}
    (oldNode : Fin P → AdmissibleKptNode family)
    (newNode : Fin Q → AdmissibleKptNode family)
    (oldLive : Nat → Fin P → Bool)
    (newLive : Nat → Fin Q → Bool)
    (horizon : Nat) where
  map : Fin P → Fin Q
  map_injective : Function.Injective map
  same_node : ∀ i : Fin P, newNode (map i) = oldNode i
  live_forward :
    ∀ cut : Nat, cut < horizon →
      ∀ i : Fin P, oldLive cut i = true →
        newLive cut (map i) = true

namespace CoherentKptIndex

/-- The identity source-index map is coherent at every cutoff. -/
def refl
    {db du dd : Nat}
    (family : List (NormalizedForbidden db du dd))
    {P : Nat}
    (node : Fin P → AdmissibleKptNode family)
    (live : Nat → Fin P → Bool)
    (horizon : Nat) :
    CoherentKptIndex family node node live live horizon where
  map := id
  map_injective := fun _ _ h => h
  same_node := by intro i; rfl
  live_forward := by
    intro cut hc i hi
    exact hi

/-- Composition keeps old literal names and live memberships.
Its available cut range is the INTERSECTION of the two ranges. -/
def comp
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q R : Nat}
    {nodeP : Fin P → AdmissibleKptNode family}
    {nodeQ : Fin Q → AdmissibleKptNode family}
    {nodeR : Fin R → AdmissibleKptNode family}
    {liveP : Nat → Fin P → Bool}
    {liveQ : Nat → Fin Q → Bool}
    {liveR : Nat → Fin R → Bool}
    {t u : Nat}
    (first : CoherentKptIndex family nodeP nodeQ liveP liveQ t)
    (second : CoherentKptIndex family nodeQ nodeR liveQ liveR u) :
    CoherentKptIndex family nodeP nodeR liveP liveR (min t u) where
  map := second.map ∘ first.map
  map_injective := second.map_injective.comp first.map_injective
  same_node := by
    intro i
    calc
      nodeR (second.map (first.map i)) = nodeQ (first.map i) :=
        second.same_node (first.map i)
      _ = nodeP i := first.same_node i
  live_forward := by
    intro cut hcut i hi
    have ht : cut < t := by omega
    have hu : cut < u := by omega
    exact second.live_forward cut hu (first.map i)
      (first.live_forward cut ht i hi)

/-- Every node's COMPLETE old ordinary/auxiliary type follows from
literal equality of the transported Kpt nodes, even at an I2 fork. -/
theorem old_type_eq
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {oldNode : Fin P → AdmissibleKptNode family}
    {newNode : Fin Q → AdmissibleKptNode family}
    {oldLive : Nat → Fin P → Bool}
    {newLive : Nat → Fin Q → Bool}
    {horizon : Nat}
    (h : CoherentKptIndex family oldNode newNode
      oldLive newLive horizon)
    (cut : Nat) (i : Fin P) :
    kptFullOldAtCut (newNode (h.map i)) cut =
      kptFullOldAtCut (oldNode i) cut := by
  rw [h.same_node i]

/-- Likewise for the COMPLETE next upper L+/E type; this is not
merely equality of an ordinary undirected-graph age shadow. -/
theorem upper_type_eq
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q : Nat}
    {oldNode : Fin P → AdmissibleKptNode family}
    {newNode : Fin Q → AdmissibleKptNode family}
    {oldLive : Nat → Fin P → Bool}
    {newLive : Nat → Fin Q → Bool}
    {horizon : Nat}
    (h : CoherentKptIndex family oldNode newNode
      oldLive newLive horizon)
    (cut : Nat) (i : Fin P) :
    kptFullUpperAtCut (newNode (h.map i)) cut =
      kptFullUpperAtCut (oldNode i) cut := by
  rw [h.same_node i]

/-- At two physical stages, the underlying source-name map is the
usual composite; no extra choice of old-source representatives. -/
theorem comp_map
    {db du dd : Nat}
    {family : List (NormalizedForbidden db du dd)}
    {P Q R : Nat}
    {nodeP : Fin P → AdmissibleKptNode family}
    {nodeQ : Fin Q → AdmissibleKptNode family}
    {nodeR : Fin R → AdmissibleKptNode family}
    {liveP : Nat → Fin P → Bool}
    {liveQ : Nat → Fin Q → Bool}
    {liveR : Nat → Fin R → Bool}
    {t u : Nat}
    (f : CoherentKptIndex family nodeP nodeQ liveP liveQ t)
    (g : CoherentKptIndex family nodeQ nodeR liveQ liveR u)
    (i : Fin P) :
    (f.comp g).map i = g.map (f.map i) := rfl

end CoherentKptIndex

end Kk
