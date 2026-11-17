# Track F — exact target prefix truncation and rank sandwich

17 November 2026. English proof and adversarial audit BEFORE Lean. The manuscript's olive single-coordinate continuation lemma requires a compatible pair to be extendable at an EXACT prescribed later target level L, whereas previous verified target continuation theorems only produce target types of level AT LEAST L. We must not silently identify these claims.

## Pure finite-type truncation

Let w=(m,U) be any valid HensonOneType ell E (its finite old neighbour pool U is K_(ell-1)-free). Given L≤m, define the actual restricted prefix type w|L=(L,U∩[0,L)). Its true old-neighbourhood clique capacity is at most cap_E(U) because the restricted pool is a subset of U. Thus the exact K_(ell-1)-free certificate persists. No new graph or Henson universality axiom is needed.

The restricted type extends to w in the complete chronological order: for each x<L, its positive bit and negative bit agree with w. If an earlier genuine type v0≤w has level(v0)≤L, then v0≤w|L by full-prefix transitivity. This is an exact source-type statement, not a claim that a target original vertex at index L exists.

## Rank sandwich

Rank is antitone on the chronological finite-type extension order. Thus if v0≤w|L≤w, then rank(w)≤rank(w|L)≤rank(v0). If rank(v0)=rank(w)=s, equality forces rank(w|L)=s. This is what upgrades 'after L' to 'at L' for an INITIALLY compatible pair. Without the initial target-rank equality, this inference need not hold.

## Fibre monotonicity under target prefix restriction

Fix actual sourceCodingFibre(Etgt,e,v) with true two-direction target old columns of ACTUAL source coding originals. If vL≤vH in the target chronological type order, then sourceCodingFibre(vH)⊆sourceCodingFibre(vL): an image original occurring beyond vH.level occurs beyond vL.level, and its two column bits agreeing with vH below vH.level in particular agree with vL below vL.level. Hence rank-largeness of sourceCodingFibre(vH) at any source node transfers to the larger target-prefix fibre(vL) by the verified Large.mono_set theorem.

## Exact-level application

Assume normalized target Henson, an arbitrary injective INDUCED graph embedding e, a genuine source type u and target v0 of EQUAL zero-based singleton rank, and the ACTUAL sourceCodingFibre(v0) rank(u)-large above u. For any exact later target level L≥v0.level, use the now verified full K4 singleton same-rank continuation (draft PR #312 until its gate passes) with bound L, obtaining genuine target vH≥v0 at level ≥L, source refinement uH≥u of same rank, and rank-large sourceCodingFibre(vH). Truncate vH at L. By the rank sandwich, rank(vH|L)=rank(v0)=rank(u); the new target level is EXACTLY L, the new target extends v0, and fibre largeness persists by target-prefix inclusion.

Thus the exact-level same-rank clause of the olive lemma can be certified, once the pure truncation lemmas and full K4 continuation theorem pass their exact named Lean gates. Its positive-rank DROP clause only requests some level beyond the prescribed bound, already handled by the uniform rank-drop theorem in #312.

## Hostile checks

1. Restrict BOTH positive and negative old bits. A target type formed by keeping only positive edges without zero-bit agreement would NOT be a chronological prefix type.
2. The restricted finite neighbour pool remains K_(ell-1)-free by genuine clique-capacity monotonicity under subset, not by a new Fraisse graph axiom.
3. The rank sandwich requires EQUAL ranks of initial and final target types, which holds for an INITIALLY compatible pair but not arbitrary source/target rank-mismatched input.
4. The restricted type vH|L is a consistent hypothetical target prefix, not necessarily a coding node of a target ORIGINAL at index L. The manuscript asks for a target TYPE at that level, so this is sufficient.
5. A source coding original whose image lies after vH.level automatically lies after L; equality of its full prefix column with vH implies equality with restricted vH|L on all coordinates <L, in both orientations.
6. The embedding e need NOT preserve original enumeration order, and fibre inclusion does not require e to be an embedding at all. Inducedness is supplied only to the K4 same-rank continuation theorem.
7. Rank largeness is monotone under SET inclusion: restricting target prefix enlarges its source fibre, not shrinks it.
8. Neither truncation nor rank sandwich gives complete multi-sort profile synchronization or diary history persistence. Global BRD claims remain pending.

## Lean acceptance

First formalize generic HensonOneType prefix restriction, safety, extension order, and rank sandwich. Then actual sourceCodingFibre monotonicity under target type extension. Only once verified full K4 same-rank theorem #312 is merged, compose them into an exact-level K4 source-target continuation. Strict standard-only transitive axioms for every step; frozen black text and full multi-sort BRD markers remain unchanged.