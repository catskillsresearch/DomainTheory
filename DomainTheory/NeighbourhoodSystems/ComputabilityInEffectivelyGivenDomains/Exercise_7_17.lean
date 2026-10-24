module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_18

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
open NeighborhoodSystem Domain.Recursive Example61
open NeighborhoodSystem Domain.Recursive ApproximableMap
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61
section
variable {α : Type*}
namespace Proposition77
variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)
/- concordance: source L4647 EXERCISE 7.17 recursion over lists -/
/-- **Exercise 7.17 (Scott 1981, PRG-19) — the pairing `pair : D^§ × D^§ → D^§` is computable.**
Its index relation is exactly `V_{2·⟨a,b⟩+2} ⊆ V_k`, a recursive slice of `D^§`'s inclusion decider
(`dsharpPresentation.incl_computable`) reindexed by the primitive-recursive node map
`s ↦ ⟨2·(p s)+2, q s⟩`, hence r.e. -/
theorem pairSharp_isComputable (P : ComputablePresentation D) :
    ComputableMap (prodPresentation (dsharpPresentation P hD) (dsharpPresentation P hD))
      (dsharpPresentation P hD) (pairSharpMap hD) := by
  constructor
  show REPred (fun s => (pairSharpMap hD).rel
    ((prodPresentation (dsharpPresentation P hD) (dsharpPresentation P hD)).X s.unpair.1)
    ((dsharpPresentation P hD).X s.unpair.2))
  have hincl : RecDecidable (fun s => Vsharp D P s.unpair.1 ⊆ Vsharp D P s.unpair.2) :=
    (dsharpPresentation P hD).incl_computable
  have hr : Nat.Primrec (fun s => Nat.pair (2 * s.unpair.1 + 2) s.unpair.2) :=
    (primrec_add₂ (primrec_mul₂ (Nat.Primrec.const 2) Nat.Primrec.left)
      (Nat.Primrec.const 2)).pair Nat.Primrec.right
  refine (RecDecidable.of_iff (fun s => ?_) (hincl.comp hr)).re
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [pairSharp_rel_Vsharp_iff hD P s.unpair.1 s.unpair.2]

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- The index characterization of `proj1Map`. `V_m proj₁ V_k` iff `k = 0` (`V_k = Γ`) or `m` is an
even node index `2a+2` with `V_{q a} ⊆ V_k` (the *right* child, `q a = a.unpair.2`). -/
theorem proj1_rel_Vsharp_iff (P : ComputablePresentation D) (m k : ℕ) :
    (proj1Map hD).rel (Vsharp D P m) (Vsharp D P k) ↔
      k = 0 ∨ (m % 2 = 0 ∧ m ≠ 0 ∧ Vsharp D P (m / 2 - 1).unpair.2 ⊆ Vsharp D P k) := by
  rw [proj1Map_rel, and_iff_right (Vsharp_mem P m), and_iff_right (Vsharp_mem P k)]
  refine or_congr (Vsharp_eq_Gamma_iff P hD k) ?_
  rcases nat_shape m with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [Vsharp_zero]
    constructor
    · rintro ⟨Pp, Qq, heq, -⟩; exact absurd heq.symm (embPair_ne_Gamma D hD Pp Qq)
    · rintro ⟨-, hne, -⟩; exact absurd rfl hne
  · rw [Vsharp_odd]
    constructor
    · rintro ⟨Pp, Qq, heq, -⟩; exact absurd heq (embZero_ne_embPair D hD (P.mem_X a) Pp Qq)
    · rintro ⟨hmod, -, -⟩; exact absurd hmod (by omega)
  · rw [Vsharp_even, show (2 * a + 2) / 2 - 1 = a from by omega]
    constructor
    · rintro ⟨Pp, Qq, heq, hQk⟩
      obtain ⟨-, hQ⟩ := embPair_injective heq
      exact ⟨by omega, by omega, by rw [hQ]; exact hQk⟩
    · rintro ⟨-, -, hsub⟩
      exact ⟨Vsharp D P a.unpair.1, Vsharp D P a.unpair.2, rfl, hsub⟩

end Proposition77
end

section
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **Exercise 7.17 (Scott 1981, PRG-19) — `proj₁` is computable.**
`V_m proj₁ V_k ↔ k = 0 ∨ (m even, m ≠ 0, V_{q(m/2-1)} ⊆ V_k)`: a disjunction of the equality and
inclusion deciders with primitive-recursive parity/right-child reindexings, hence r.e. -/
theorem proj1_isComputable (P : ComputablePresentation D) :
    ComputableMap (dsharpPresentation P hD) (dsharpPresentation P hD) (proj1Map hD) := by
  constructor
  show REPred (fun s => (proj1Map hD).rel (Vsharp D P s.unpair.1) (Vsharp D P s.unpair.2))
  have hk0 : RecDecidable (fun s => s.unpair.2 = 0) :=
    RecDecidable.natEq Nat.Primrec.right (Nat.Primrec.const 0)
  have hmod : RecDecidable (fun s => s.unpair.1 % 2 = 0) :=
    RecDecidable.natEq (primrec_mod2.comp Nat.Primrec.left) (Nat.Primrec.const 0)
  have hne : RecDecidable (fun s => s.unpair.1 ≠ 0) :=
    (RecDecidable.natEq Nat.Primrec.left (Nat.Primrec.const 0)).not
  have hg : Nat.Primrec (fun s => Nat.pair (s.unpair.1 / 2 - 1).unpair.2 s.unpair.2) :=
    (Nat.Primrec.right.comp (primrec_sub₂ (primrec_div2.comp Nat.Primrec.left)
      (Nat.Primrec.const 1))).pair Nat.Primrec.right
  have hincl : RecDecidable (fun s => Vsharp D P (s.unpair.1 / 2 - 1).unpair.2 ⊆
      Vsharp D P s.unpair.2) := by
    refine RecDecidable.of_iff (fun s => ?_) ((dsharpPresentation P hD).incl_computable.comp hg)
    simp only [dsharpPresentation_X, unpair_pair_fst, unpair_pair_snd]
  exact (RecDecidable.of_iff (fun s => proj1_rel_Vsharp_iff hD P s.unpair.1 s.unpair.2)
    (hk0.or (hmod.and (hne.and hincl)))).re

end Proposition77
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Proposition77
section
set_option linter.unusedVariables false

theorem example_717.{u_1} : And
  (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X)
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum (Prod (List Bool) α) (Prod (List Bool) α))
      (Prod (List Bool) α)
      (@DomainTheory.NeighbourhoodSystems.prod (Prod (List Bool) α) (Prod (List Bool) α)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
      (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
      (@DomainTheory.NeighbourhoodSystems.prodPresentation (Prod (List Bool) α) (Prod (List Bool) α)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
        (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
        (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD))
      (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD))
  (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X)
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (Prod (List Bool) α) (Prod (List Bool) α)
      (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
      (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.proj1Map α D hD)) :=
  @And.intro
  (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X)
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum (Prod (List Bool) α) (Prod (List Bool) α))
      (Prod (List Bool) α)
      (@DomainTheory.NeighbourhoodSystems.prod (Prod (List Bool) α) (Prod (List Bool) α)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
      (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
      (@DomainTheory.NeighbourhoodSystems.prodPresentation (Prod (List Bool) α) (Prod (List Bool) α)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
        (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
        (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD))
      (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD))
  (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    (hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X)
    (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D),
    @DomainTheory.NeighbourhoodSystems.ComputableMap (Prod (List Bool) α) (Prod (List Bool) α)
      (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
      (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD)
      (@DomainTheory.NeighbourhoodSystems.Proposition77.proj1Map α D hD))
  @DomainTheory.NeighbourhoodSystems.Proposition77.pairSharp_isComputable
  @DomainTheory.NeighbourhoodSystems.Proposition77.proj1_isComputable
end

end DomainTheory.NeighbourhoodSystems.Proposition77
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61
variable {α : Type*}

namespace Proposition77

variable {D : NeighborhoodSystem α} (hD : ∀ X, D.mem X → X.Nonempty)


/-- **`proj1Map` really is the second projection of the pair part:** `proj₁(⟨x, y⟩^§) = y`. -/
theorem proj1_toElementMap_pairSharp (x y : (Dsharp D hD).Element) :
    (proj1Map hD).toElementMap (pairSharp D hD x y) = y := by
  apply Element.ext
  intro Z
  simp only [ApproximableMap.mem_toElementMap, proj1Map_rel]
  constructor
  · rintro ⟨W, hWmem, hMW, hMZ, hdisj⟩
    rcases hWmem with rfl | ⟨Pp, Qq, hxP, hyQ, rfl⟩
    · rcases hdisj with rfl | ⟨Pp', Qq', hPe, -⟩
      · exact y.master_mem
      · exact absurd hPe.symm (embPair_ne_Gamma D hD Pp' Qq')
    · rcases hdisj with rfl | ⟨Pp', Qq', hPe, hQ'Z⟩
      · exact y.master_mem
      · obtain ⟨-, hQQ⟩ := embPair_injective hPe
        exact y.up_mem hyQ hMZ (by rw [hQQ]; exact hQ'Z)
  · intro hyZ
    exact ⟨embPair (Gamma D) Z, Or.inr ⟨Gamma D, Z, x.master_mem, hyZ, rfl⟩,
      MemS.pair MemS.gamma (y.sub hyZ), y.sub hyZ, Or.inr ⟨Gamma D, Z, rfl, subset_rfl⟩⟩

end Proposition77
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

/-- **The universal strict map `g : D^§ → E`, as a neighbourhood relation.** Defined by recursion on
the `D^§`-neighbourhood shape: `Γ ↦ Δ_E`, `0·X ↦ u`'s relation, `1·P∪2·Q ↦ v ∘ (g × g)`. -/
inductive GRel (u : ApproximableMap D E) (v : ApproximableMap (prod E E) E) :
    Set (List Bool × α) → Set β → Prop
  | gamma {Z} : Z = E.master → GRel u v (Gamma D) Z
  | leaf {X Z} : u.rel X Z → GRel u v (embZero X) Z
  | node {P Q Z₁ Z₂ Z} : GRel u v P Z₁ → GRel u v Q Z₂ →
      v.rel (prodNbhd Z₁ Z₂) Z → GRel u v (embPair P Q) Z

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- `embZero X ≠ embPair P Q` from `P ∈ 𝒟^§` (no `D.mem X` needed). -/
theorem embZero_ne_embPair_of_memS (hD : ∀ X, D.mem X → X.Nonempty)
    {X : Set α} {P Q : Set (List Bool × α)} (hP : MemS D P) :
    embZero X ≠ embPair P Q := by
  intro h
  obtain ⟨z, hz⟩ := embPair_nonempty (memS_nonempty hD hP) (Q := Q)
  have hz0 : z ∈ embZero X := h ▸ hz
  have hpath : z.1 = [] := hz0.1
  rcases hz with ⟨p', hp', -⟩ | ⟨q', hq', -⟩
  · rw [hp'] at hpath; simp at hpath
  · rw [hq'] at hpath; simp at hpath

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Related outputs are `E`-neighbourhoods. -/
theorem gRel_cod {W Z} (h : GRel u v W Z) : E.mem Z := by
  induction h with
  | gamma hZ => exact hZ ▸ E.master_mem
  | leaf hrel => exact u.rel_cod hrel
  | node _ _ hvrel _ _ => exact v.rel_cod hvrel

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Related inputs are `D^§`-neighbourhoods. -/
theorem gRel_dom {W Z} (h : GRel u v W Z) : MemS D W := by
  induction h with
  | gamma _ => exact MemS.gamma
  | leaf hrel => exact MemS.zero (u.rel_dom hrel)
  | node _ _ _ ihP ihQ => exact MemS.pair ihP ihQ

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Inversion at a node `1·P ∪ 2·Q`: `(1·P∪2·Q) g Z ↔ ∃ Z₁ Z₂, P g Z₁ ∧ Q g Z₂ ∧ ⟨Z₁,Z₂⟩ v Z`. -/
theorem gRel_embPair_inv (hD : ∀ X, D.mem X → X.Nonempty) {P Q : Set (List Bool × α)} {Z}
    (h : GRel u v (embPair P Q) Z) :
    ∃ Z₁ Z₂, GRel u v P Z₁ ∧ GRel u v Q Z₂ ∧ v.rel (prodNbhd Z₁ Z₂) Z := by
  have hPQ := gRel_dom h
  obtain ⟨hPmem, hQmem⟩ := memS_embPair_inv hD hPQ
  generalize hW : embPair P Q = W at h
  cases h with
  | gamma hZ => exact absurd hW (embPair_ne_Gamma D hD P Q)
  | @leaf X Z hrel => exact absurd hW.symm (embZero_ne_embPair_of_memS hD hPmem)
  | @node P' Q' Z₁ Z₂ Z hP' hQ' hvrel =>
      obtain ⟨rfl, rfl⟩ := embPair_injective hW
      exact ⟨Z₁, Z₂, hP', hQ', hvrel⟩

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Inversion at a leaf `0·X`: `0·X g Z ↔ X u Z`. -/
theorem gRel_embZero_inv (hD : ∀ X, D.mem X → X.Nonempty) {X : Set α} {Z}
    (h : GRel u v (embZero X) Z) : u.rel X Z := by
  generalize hW : embZero X = W at h
  cases h with
  | gamma hZ => exact absurd hW (embZero_ne_Gamma D hD X)
  | @leaf X' Z' hrel => rw [embZero_injective hW]; exact hrel
  | @node P Q Z₁ Z₂ Z hP hQ hvrel =>
      exact absurd hW (embZero_ne_embPair_of_memS hD (gRel_dom hP))

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Inversion at `Γ`: `Γ g Z` forces `Z = Δ_E` (Scott's strictness). -/
theorem gRel_gamma_inv (hD : ∀ X, D.mem X → X.Nonempty) {Z}
    (h : GRel u v (Gamma D) Z) : Z = E.master := by
  generalize hW : Gamma D = W at h
  cases h with
  | gamma hZ => exact hZ
  | @leaf X Z hrel => exact absurd hW.symm (embZero_ne_Gamma D hD X)
  | @node P Q Z₁ Z₂ Z hP hQ hvrel => exact absurd hW.symm (embPair_ne_Gamma D hD P Q)

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Intersectivity on the output (Scott's 2.1(ii)). -/
theorem gRel_interRight (hD : ∀ X, D.mem X → X.Nonempty) {W Z} (h : GRel u v W Z) :
    ∀ {Z'}, GRel u v W Z' → GRel u v W (Z ∩ Z') := by
  induction h with
  | @gamma Z hZ =>
      intro Z' h'
      subst hZ
      have hZ' := gRel_gamma_inv hD h'
      subst hZ'
      rw [Set.inter_self]
      exact GRel.gamma rfl
  | @leaf X Z hrel =>
      intro Z' h'
      exact GRel.leaf (u.inter_right hrel (gRel_embZero_inv hD h'))
  | @node P Q Z₁ Z₂ Z hP hQ hvrel ihP ihQ =>
      intro Z' h'
      obtain ⟨Z₁', Z₂', hP', hQ', hv'⟩ := gRel_embPair_inv hD h'
      have hgP : GRel u v P (Z₁ ∩ Z₁') := ihP hP'
      have hgQ : GRel u v Q (Z₂ ∩ Z₂') := ihQ hQ'
      refine GRel.node hgP hgQ ?_
      have hmem : (prod E E).mem (prodNbhd (Z₁ ∩ Z₁') (Z₂ ∩ Z₂')) :=
        prod_mem_prodNbhd (gRel_cod hgP) (gRel_cod hgQ)
      have hv1 : v.rel (prodNbhd (Z₁ ∩ Z₁') (Z₂ ∩ Z₂')) Z :=
        v.mono hvrel (prodNbhd_subset_iff.mpr ⟨Set.inter_subset_left, Set.inter_subset_left⟩)
          subset_rfl hmem (v.rel_cod hvrel)
      have hv2 : v.rel (prodNbhd (Z₁ ∩ Z₁') (Z₂ ∩ Z₂')) Z' :=
        v.mono hv' (prodNbhd_subset_iff.mpr ⟨Set.inter_subset_right, Set.inter_subset_right⟩)
          subset_rfl hmem (v.rel_cod hv')
      exact v.inter_right hv1 hv2

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **Strictness in the relation: every `D^§`-neighbourhood folds to `Δ_E`.** This is why no separate
"top" clause is needed — `u`/`v` relate `Δ ↦ Δ`, so the master propagates through the tree. -/
theorem gRel_master : ∀ {W}, MemS D W → GRel u v W E.master := by
  intro W hW
  induction hW with
  | gamma => exact GRel.gamma rfl
  | @zero X hX =>
      exact GRel.leaf ((u.rel_iff_mem_principal hX).mpr (u.toElementMap _).master_mem)
  | @pair P Q _ _ ihP ihQ =>
      refine GRel.node ihP ihQ ?_
      have h := v.master_rel
      rwa [prod_master] at h

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- Monotonicity (Scott's 2.1(iii)). -/
theorem gRel_mono (hD : ∀ X, D.mem X → X.Nonempty) {W Z} (h : GRel u v W Z) :
    ∀ {W' Z'}, W' ⊆ W → Z ⊆ Z' → MemS D W' → E.mem Z' → GRel u v W' Z' := by
  induction h with
  | @gamma Z hZ =>
      intro W' Z' hW'W hZZ' hW'mem hZ'mem
      subst hZ
      have hZ' : Z' = E.master := Set.Subset.antisymm (E.sub_master hZ'mem) hZZ'
      subst hZ'
      exact gRel_master hW'mem
  | @leaf X Z hrel =>
      intro W' Z' hW'W hZZ' hW'mem hZ'mem
      obtain ⟨X', hX'mem, rfl⟩ := memS_sub_embZero hD hW'mem hW'W
      exact GRel.leaf (u.mono hrel (embZero_subset.mp hW'W) hZZ' hX'mem hZ'mem)
  | @node P Q Z₁ Z₂ Z hP hQ hvrel ihP ihQ =>
      intro W' Z' hW'W hZZ' hW'mem hZ'mem
      obtain ⟨P', Q', hP'mem, hQ'mem, rfl⟩ := memS_sub_embPair hD hW'mem hW'W
      obtain ⟨hP'P, hQ'Q⟩ := embPair_subset.mp hW'W
      refine GRel.node (ihP hP'P subset_rfl hP'mem (gRel_cod hP))
        (ihQ hQ'Q subset_rfl hQ'mem (gRel_cod hQ)) ?_
      exact v.mono hvrel subset_rfl hZZ'
        (prod_mem_prodNbhd (gRel_cod hP) (gRel_cod hQ)) hZ'mem

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **Exercise 7.17 Part 2 — the universal strict map `g : D^§ → E`.** -/
def gMap (u : ApproximableMap D E) (v : ApproximableMap (prod E E) E)
    (hD : ∀ X, D.mem X → X.Nonempty) : ApproximableMap (Dsharp D hD) E where
  rel := GRel u v
  rel_dom h := gRel_dom h
  rel_cod h := gRel_cod h
  master_rel := GRel.gamma rfl
  inter_right h h' := gRel_interRight hD h h'
  mono h hsub hsup hX' hY' := gRel_mono hD h hsub hsup hX' hY'

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

@[simp] theorem gMap_rel {hD : ∀ X, D.mem X → X.Nonempty} {W : Set (List Bool × α)} {Z : Set β} :
    (gMap u v hD).rel W Z ↔ GRel u v W Z := Iff.rfl

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)

/-- **The certificate step.** Input `p = ⟨w, tbl⟩` with `w = ⟨n, cert⟩` and `tbl` the memo table.
`cert` decodes to `⟨out, wit, lcert, rcert⟩`. Returns `⟨okBit, out⟩`:
* `n = 0`   : `okBit = fe⟨out, mIdx⟩` (is `Q_out = Δ_E`?);
* `n = 2a+1`: `okBit = fU⟨wit, ⟨a, out⟩⟩` (does `wit` witness `X_a u Q_out`?);
* `n = 2a+2`: read children `⟨a.1, lcert⟩`, `⟨a.2, rcert⟩` from `tbl`; `okBit = okL·okR·
  fV⟨wit, ⟨⟨outL, outR⟩, out⟩⟩`. -/
def gStep (p : ℕ) : ℕ :=
  let w := p.unpair.1
  let tbl := p.unpair.2
  let nn := w.unpair.1
  let cert := w.unpair.2
  let out := cert.unpair.1
  let wit := cert.unpair.2.unpair.1
  let lcert := cert.unpair.2.unpair.2.unpair.1
  let rcert := cert.unpair.2.unpair.2.unpair.2
  let b := nn / 2 - 1
  let childL := listGet tbl (w - 1 - Nat.pair b.unpair.1 lcert)
  let childR := listGet tbl (w - 1 - Nat.pair b.unpair.2 rcert)
  selectFn (1 - nn)
    (Nat.pair (fe (Nat.pair out mIdx)) out)
    (selectFn (nn % 2)
      (Nat.pair (fU (Nat.pair wit (Nat.pair (nn / 2) out))) out)
      (Nat.pair (childL.unpair.1 * childR.unpair.1
          * fV (Nat.pair wit (Nat.pair (Nat.pair childL.unpair.2 childR.unpair.2) out))) out))

end Computability

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)

/-- The full evaluator: the course-of-values value of `gStep` at `w = ⟨n, cert⟩`. -/
def gEval : ℕ → ℕ := gOf (gStep fe fU fV mIdx)

end Computability

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)


theorem gEval_pair (n cert : ℕ) :
    gEval fe fU fV mIdx (Nat.pair n cert)
      = gStep fe fU fV mIdx
          (Nat.pair (Nat.pair n cert) (rtbl (gStep fe fU fV mIdx) (Nat.pair n cert))) := by
  rw [gEval, gOf_def]

end Computability
end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


/-- **`g(in x) = u(x)`.** The injection summand of `D^§ ≅ D + (D^§×D^§)` folds via `u`. -/
theorem gMap_in (hD : ∀ X, D.mem X → X.Nonempty) (x : D.Element) :
    (gMap u v hD).toElementMap (inSharp D hD x) = u.toElementMap x := by
  apply Element.ext
  intro Z
  simp only [mem_toElementMap, gMap_rel]
  constructor
  · rintro ⟨W, hWmem, hrel⟩
    rcases hWmem with rfl | ⟨X, hXx, rfl⟩
    · have hZ := gRel_gamma_inv hD hrel; subst hZ
      exact ⟨D.master, x.master_mem, u.master_rel⟩
    · exact ⟨X, hXx, gRel_embZero_inv hD hrel⟩
  · rintro ⟨X, hXx, hrel⟩
    exact ⟨embZero X, Or.inr ⟨X, hXx, rfl⟩, GRel.leaf hrel⟩

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


/-- **`g(pair y z) = v(⟨g y, g z⟩)`.** The product summand folds via `v` applied to the recursive
results — the defining recursion of the catamorphism. -/
theorem gMap_pair (hD : ∀ X, D.mem X → X.Nonempty) (y z : (Dsharp D hD).Element) :
    (gMap u v hD).toElementMap (pairSharp D hD y z)
      = v.toElementMap (pair ((gMap u v hD).toElementMap y) ((gMap u v hD).toElementMap z)) := by
  apply Element.ext
  intro Z
  simp only [mem_toElementMap, gMap_rel]
  constructor
  · rintro ⟨W, hWmem, hrel⟩
    rcases hWmem with rfl | ⟨P, Q, hPy, hQz, rfl⟩
    · have hZ := gRel_gamma_inv hD hrel; subst hZ
      exact ⟨(prod E E).master, (pair _ _).master_mem, v.master_rel⟩
    · obtain ⟨Z₁, Z₂, hP1, hQ2, hvrel⟩ := gRel_embPair_inv hD hrel
      exact ⟨prodNbhd Z₁ Z₂,
        mem_pair.mpr ⟨Z₁, Z₂, ⟨P, hPy, hP1⟩, ⟨Q, hQz, hQ2⟩, rfl⟩, hvrel⟩
  · rintro ⟨V, hVmem, hvrel⟩
    obtain ⟨Z₁, Z₂, ⟨P, hPy, hP1⟩, ⟨Q, hQz, hQ2⟩, rfl⟩ := mem_pair.mp hVmem
    exact ⟨embPair P Q, Or.inr ⟨P, Q, hPy, hQz, rfl⟩, GRel.node hP1 hQ2 hvrel⟩

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


/-- **`g` is strict** (`g(⊥) = ⊥`): Scott's "the unique *strict* mapping". -/
theorem gMap_strict (hD : ∀ X, D.mem X → X.Nonempty) :
    IsStrict (gMap u v hD) := fun _ h => gRel_gamma_inv hD h

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)


theorem gStep_gamma (cert tbl : ℕ) :
    gStep fe fU fV mIdx (Nat.pair (Nat.pair 0 cert) tbl)
      = Nat.pair (fe (Nat.pair cert.unpair.1 mIdx)) cert.unpair.1 := by
  simp only [gStep, unpair_pair_fst, unpair_pair_snd, Nat.sub_zero, selectFn_one]

end Computability
end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)


theorem gStep_leaf (a cert tbl : ℕ) :
    gStep fe fU fV mIdx (Nat.pair (Nat.pair (2 * a + 1) cert) tbl)
      = Nat.pair (fU (Nat.pair cert.unpair.2.unpair.1 (Nat.pair a cert.unpair.1)))
          cert.unpair.1 := by
  simp only [gStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 1) = 0 by omega, selectFn_zero,
    show (2 * a + 1) % 2 = 1 by omega, selectFn_one, show (2 * a + 1) / 2 = a by omega]

end Computability
end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)


theorem gStep_node (a cert tbl : ℕ) :
    gStep fe fU fV mIdx (Nat.pair (Nat.pair (2 * a + 2) cert) tbl)
      = Nat.pair
          ((listGet tbl (Nat.pair (2 * a + 2) cert - 1
                - Nat.pair a.unpair.1 cert.unpair.2.unpair.2.unpair.1)).unpair.1
            * (listGet tbl (Nat.pair (2 * a + 2) cert - 1
                - Nat.pair a.unpair.2 cert.unpair.2.unpair.2.unpair.2)).unpair.1
            * fV (Nat.pair cert.unpair.2.unpair.1
                (Nat.pair (Nat.pair
                    (listGet tbl (Nat.pair (2 * a + 2) cert - 1
                      - Nat.pair a.unpair.1 cert.unpair.2.unpair.2.unpair.1)).unpair.2
                    (listGet tbl (Nat.pair (2 * a + 2) cert - 1
                      - Nat.pair a.unpair.2 cert.unpair.2.unpair.2.unpair.2)).unpair.2)
                  cert.unpair.1)))
          cert.unpair.1 := by
  simp only [gStep, unpair_pair_fst, unpair_pair_snd]
  rw [show (1 : ℕ) - (2 * a + 2) = 0 by omega, selectFn_zero,
    show (2 * a + 2) % 2 = 0 by omega, selectFn_zero, show (2 * a + 2) / 2 - 1 = a by omega]

end Computability
end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)


/-- The output index of `gEval ⟨n, cert⟩` is just `cert`'s first component (all three branches emit
`out`). -/
theorem gEval_out (n cert : ℕ) :
    (gEval fe fU fV mIdx (Nat.pair n cert)).unpair.2 = cert.unpair.1 := by
  rw [gEval_pair]
  rcases nat_shape n with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
  · rw [gStep_gamma, unpair_pair_snd]
  · rw [gStep_leaf, unpair_pair_snd]
  · rw [gStep_node, unpair_pair_snd]

end Computability
end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)


/-- Memo lookup, in `gEval` form: at any earlier code `w' < w`, position `w-1-w'` of the table is
`gEval w'`. -/
theorem listGet_rtbl_gEval {w' w : ℕ} (h : w' < w) :
    listGet (rtbl (gStep fe fU fV mIdx) w) (w - 1 - w') = gEval fe fU fV mIdx w' :=
  listGet_rtbl (gStep fe fU fV mIdx) h

end Computability
end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


/-- `Nat.pair` is monotone in its second argument (first argument fixed). -/
theorem pair_le_pair_right {a b d : ℕ} (h : b ≤ d) : Nat.pair a b ≤ Nat.pair a d := by
  unfold Nat.pair
  rcases Nat.lt_or_ge a b with hab | hab
  · rw [ite_eq_left hab, ite_eq_left (lt_of_lt_of_le hab h)]
    have : b * b ≤ d * d := Nat.mul_le_mul h h
    omega
  · rw [ite_eq_right (Nat.not_lt.mpr hab)]
    rcases Nat.lt_or_ge a d with had | had
    · rw [ite_eq_left had]
      have h1 : a * a + a ≤ d * d := by
        calc a * a + a = a * (a + 1) := by ring
          _ ≤ a * d := Nat.mul_le_mul (le_refl a) had
          _ ≤ d * d := Nat.mul_le_mul had.le (le_refl d)
      omega
    · rw [ite_eq_right (Nat.not_lt.mpr had)]; omega

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


/-- `Nat.pair` is strictly monotone in its first argument (second argument fixed). -/
theorem pair_lt_pair_left {a c b : ℕ} (h : a < c) : Nat.pair a b < Nat.pair c b := by
  unfold Nat.pair
  rcases Nat.lt_or_ge a b with hab | hab
  · rw [ite_eq_left hab]
    rcases Nat.lt_or_ge c b with hcb | hcb
    · rw [ite_eq_left hcb]; omega
    · rw [ite_eq_right (Nat.not_lt.mpr hcb)]
      have hbc : b * b ≤ c * c := Nat.mul_le_mul hcb hcb
      omega
  · rw [ite_eq_right (Nat.not_lt.mpr hab),
      ite_eq_right (Nat.not_lt.mpr (le_of_lt (lt_of_le_of_lt hab h)))]
    have hcc : (a + 1) * (a + 1) ≤ c * c := Nat.mul_le_mul h h
    have hexp : (a + 1) * (a + 1) = a * a + 2 * a + 1 := by ring
    omega

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


/-- Combined: strict in the first argument, monotone in the second. -/
theorem pair_lt_pair_of_lt_le {a c b d : ℕ} (hac : a < c) (hbd : b ≤ d) :
    Nat.pair a b < Nat.pair c d :=
  lt_of_lt_of_le (pair_lt_pair_left hac) (pair_le_pair_right hbd)

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)


set_option maxHeartbeats 1000000 in
/-- **Completeness of the certificate.** If `g` relates `V_n` to some `Z`, there is a `cert` the memo
certifies (ok-bit `1`) with `Q_{out} = Z`. Strong induction on `n`; the node case builds the certificate
from the children's certificates (children codes are `<` by `pair_lt_pair_of_lt_le`). -/
theorem gEval_complete (hD : ∀ X, D.mem X → X.Nonempty)
    (P : ComputablePresentation D) (Q : ComputablePresentation E)
    (hEq : ∀ m, fe (Nat.pair m mIdx) = 1 ↔ Q.X m = E.master) (hMidx : Q.X mIdx = E.master)
    (hU : ∀ a m, (∃ i, fU (Nat.pair i (Nat.pair a m)) = 1) ↔ u.rel (P.X a) (Q.X m))
    (hV : ∀ k1 k2 m, (∃ i, fV (Nat.pair i (Nat.pair (Nat.pair k1 k2) m)) = 1) ↔
        v.rel (prodNbhd (Q.X k1) (Q.X k2)) (Q.X m)) :
    ∀ n Z, GRel u v (Vsharp D P n) Z →
      ∃ cert, (gEval fe fU fV mIdx (Nat.pair n cert)).unpair.1 = 1
        ∧ Q.X cert.unpair.1 = Z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro Z hg
    rcases nat_shape n with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
    · -- n = 0
      rw [Vsharp_zero] at hg
      have hZ := gRel_gamma_inv hD hg
      refine ⟨Nat.pair mIdx (Nat.pair 0 0), ?_, ?_⟩
      · rw [gEval_pair, gStep_gamma, unpair_pair_fst, unpair_pair_fst]
        exact (hEq mIdx).mpr hMidx
      · rw [unpair_pair_fst, hMidx, hZ]
    · -- n = 2a+1
      rw [Vsharp_odd] at hg
      have hu := gRel_embZero_inv hD hg
      obtain ⟨e, he⟩ := Q.surj (u.rel_cod hu)
      rw [← he] at hu
      obtain ⟨wit, hwit⟩ := (hU a e).mpr hu
      refine ⟨Nat.pair e (Nat.pair wit 0), ?_, ?_⟩
      · rw [gEval_pair, gStep_leaf, unpair_pair_fst, unpair_pair_snd, unpair_pair_fst,
          unpair_pair_fst]
        exact hwit
      · rw [unpair_pair_fst]; exact he
    · -- n = 2a+2
      rw [Vsharp_even] at hg
      obtain ⟨Z₁, Z₂, hg1, hg2, hvrel⟩ := gRel_embPair_inv hD hg
      obtain ⟨certL, hokL, heqL⟩ := ih a.unpair.1 (by have := unpair_fst_le a; omega) Z₁ hg1
      obtain ⟨certR, hokR, heqR⟩ := ih a.unpair.2 (by have := unpair_snd_le a; omega) Z₂ hg2
      obtain ⟨e, he⟩ := Q.surj (v.rel_cod hvrel)
      rw [← heqL, ← heqR, ← he] at hvrel
      obtain ⟨wit, hwit⟩ := (hV certL.unpair.1 certR.unpair.1 e).mpr hvrel
      refine ⟨Nat.pair e (Nat.pair wit (Nat.pair certL certR)), ?_, ?_⟩
      · rw [gEval_pair, gStep_node, unpair_pair_fst]
        have hcertL : certL ≤ Nat.pair e (Nat.pair wit (Nat.pair certL certR)) :=
          le_trans (Domain.Recursive.le_pair_left _ _)
            (le_trans (Domain.Recursive.le_pair_right wit _) (Domain.Recursive.le_pair_right e _))
        have hcertR : certR ≤ Nat.pair e (Nat.pair wit (Nat.pair certL certR)) :=
          le_trans (Domain.Recursive.le_pair_right _ _)
            (le_trans (Domain.Recursive.le_pair_right wit _) (Domain.Recursive.le_pair_right e _))
        have hlt1 : Nat.pair a.unpair.1 certL < Nat.pair (2 * a + 2)
            (Nat.pair e (Nat.pair wit (Nat.pair certL certR))) :=
          pair_lt_pair_of_lt_le (by have := unpair_fst_le a; omega) hcertL
        have hlt2 : Nat.pair a.unpair.2 certR < Nat.pair (2 * a + 2)
            (Nat.pair e (Nat.pair wit (Nat.pair certL certR))) :=
          pair_lt_pair_of_lt_le (by have := unpair_snd_le a; omega) hcertR
        simp only [unpair_pair_fst, unpair_pair_snd]
        rw [listGet_rtbl_gEval fe fU fV mIdx hlt1, listGet_rtbl_gEval fe fU fV mIdx hlt2,
          gEval_out, gEval_out]
        rw [show (gEval fe fU fV mIdx (Nat.pair a.unpair.1 certL)).unpair.1 = 1 from hokL,
          show (gEval fe fU fV mIdx (Nat.pair a.unpair.2 certR)).unpair.1 = 1 from hokR]
        simp only [Nat.one_mul]
        exact hwit
      · rw [unpair_pair_fst]; exact he

end Computability
end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)


/-- The certificate step is primitive recursive (when the underlying functions are). -/
theorem primrec_gStep (hfe : Nat.Primrec fe) (hfU : Nat.Primrec fU) (hfV : Nat.Primrec fV) :
    Nat.Primrec (gStep fe fU fV mIdx) := by
  have hw : Nat.Primrec (fun p : ℕ => p.unpair.1) := Nat.Primrec.left
  have htbl : Nat.Primrec (fun p : ℕ => p.unpair.2) := Nat.Primrec.right
  have hnn : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1) := Nat.Primrec.left.comp Nat.Primrec.left
  have hcert : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hout : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2.unpair.1) := Nat.Primrec.left.comp hcert
  have hwit : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp hcert)
  have hlc : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1) :=
    Nat.Primrec.left.comp (Nat.Primrec.right.comp (Nat.Primrec.right.comp hcert))
  have hrc : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2) :=
    Nat.Primrec.right.comp (Nat.Primrec.right.comp (Nat.Primrec.right.comp hcert))
  have hb : Nat.Primrec (fun p : ℕ => p.unpair.1.unpair.1 / 2 - 1) :=
    primrec_sub₂ (primrec_div2.comp hnn) (Nat.Primrec.const 1)
  have hlpos : Nat.Primrec (fun p : ℕ =>
      p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
        p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1) :=
    primrec_sub₂ (primrec_sub₂ hw (Nat.Primrec.const 1))
      ((Nat.Primrec.left.comp hb).pair hlc)
  have hrpos : Nat.Primrec (fun p : ℕ =>
      p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
        p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2) :=
    primrec_sub₂ (primrec_sub₂ hw (Nat.Primrec.const 1))
      ((Nat.Primrec.right.comp hb).pair hrc)
  have hchildL : Nat.Primrec (fun p : ℕ => listGet p.unpair.2
      (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
        p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1)) :=
    primrec_listGet₂ htbl hlpos
  have hchildR : Nat.Primrec (fun p : ℕ => listGet p.unpair.2
      (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
        p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2)) :=
    primrec_listGet₂ htbl hrpos
  have hgamma : Nat.Primrec (fun p : ℕ =>
      Nat.pair (fe (Nat.pair p.unpair.1.unpair.2.unpair.1 mIdx)) p.unpair.1.unpair.2.unpair.1) :=
    (hfe.comp (hout.pair (Nat.Primrec.const mIdx))).pair hout
  have hleaf : Nat.Primrec (fun p : ℕ =>
      Nat.pair (fU (Nat.pair p.unpair.1.unpair.2.unpair.2.unpair.1
          (Nat.pair (p.unpair.1.unpair.1 / 2) p.unpair.1.unpair.2.unpair.1)))
        p.unpair.1.unpair.2.unpair.1) :=
    (hfU.comp (hwit.pair ((primrec_div2.comp hnn).pair hout))).pair hout
  have hfVcall : Nat.Primrec (fun p : ℕ =>
      fV (Nat.pair p.unpair.1.unpair.2.unpair.2.unpair.1
        (Nat.pair (Nat.pair
            (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
              p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1)).unpair.2
            (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
              p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2)).unpair.2)
          p.unpair.1.unpair.2.unpair.1))) :=
    hfV.comp (hwit.pair
      (((Nat.Primrec.right.comp hchildL).pair (Nat.Primrec.right.comp hchildR)).pair hout))
  have hnode : Nat.Primrec (fun p : ℕ =>
      Nat.pair ((listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
              p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1)).unpair.1
          * (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
              p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2)).unpair.1
          * fV (Nat.pair p.unpair.1.unpair.2.unpair.2.unpair.1
              (Nat.pair (Nat.pair
                  (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.1
                    p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.1)).unpair.2
                  (listGet p.unpair.2 (p.unpair.1 - 1 - Nat.pair (p.unpair.1.unpair.1 / 2 - 1).unpair.2
                    p.unpair.1.unpair.2.unpair.2.unpair.2.unpair.2)).unpair.2)
                p.unpair.1.unpair.2.unpair.1)))
        p.unpair.1.unpair.2.unpair.1) :=
    (primrec_mul₂ (primrec_mul₂ (Nat.Primrec.left.comp hchildL) (Nat.Primrec.left.comp hchildR))
      hfVcall).pair hout
  refine (primrec_selectFn (primrec_sub₂ (Nat.Primrec.const 1) hnn) hgamma
    (primrec_selectFn (primrec_mod2.comp hnn) hleaf hnode)).of_eq fun p => rfl

end Computability
end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


/-- A decoded sub-component is `≤` the code it is decoded from. -/
theorem unpair_snd_snd_fst_le (c : ℕ) : c.unpair.2.unpair.2.unpair.1 ≤ c := by
  have h1 := unpair_snd_le c
  have h2 := unpair_snd_le c.unpair.2
  have h3 := unpair_fst_le c.unpair.2.unpair.2
  omega

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


theorem unpair_snd_snd_snd_le (c : ℕ) : c.unpair.2.unpair.2.unpair.2 ≤ c := by
  have h1 := unpair_snd_le c
  have h2 := unpair_snd_le c.unpair.2
  have h3 := unpair_snd_le c.unpair.2.unpair.2
  omega

end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


section Computability

variable (fe fU fV : ℕ → ℕ) (mIdx : ℕ)


/-- **Soundness of the certificate.** If the memo certifies `⟨n, cert⟩` (ok-bit `1`), then `g` relates
`V_n` to `Q_{out}` (`out = cert.unpair.1`). Strong induction on the combined code `⟨n, cert⟩`; the node
case reads the two children from the memo table (`listGet_rtbl`) and applies the IH. -/
theorem gEval_sound
    (P : ComputablePresentation D) (Q : ComputablePresentation E)
    (hEq : ∀ m, fe (Nat.pair m mIdx) = 1 ↔ Q.X m = E.master)
    (hU : ∀ a m, (∃ i, fU (Nat.pair i (Nat.pair a m)) = 1) ↔ u.rel (P.X a) (Q.X m))
    (hV : ∀ k1 k2 m, (∃ i, fV (Nat.pair i (Nat.pair (Nat.pair k1 k2) m)) = 1) ↔
        v.rel (prodNbhd (Q.X k1) (Q.X k2)) (Q.X m)) :
    ∀ n cert, (gEval fe fU fV mIdx (Nat.pair n cert)).unpair.1 = 1 →
      GRel u v (Vsharp D P n) (Q.X cert.unpair.1) := by
  have key : ∀ w n cert, Nat.pair n cert = w →
      (gEval fe fU fV mIdx (Nat.pair n cert)).unpair.1 = 1 →
        GRel u v (Vsharp D P n) (Q.X cert.unpair.1) := by
    intro w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro n cert hw hok
      rcases nat_shape n with rfl | ⟨a, rfl⟩ | ⟨a, rfl⟩
      · rw [gEval_pair, gStep_gamma, unpair_pair_fst] at hok
        rw [Vsharp_zero]
        exact GRel.gamma ((hEq cert.unpair.1).mp hok)
      · rw [gEval_pair, gStep_leaf, unpair_pair_fst] at hok
        rw [Vsharp_odd]
        exact GRel.leaf ((hU a cert.unpair.1).mp ⟨cert.unpair.2.unpair.1, hok⟩)
      · rw [Vsharp_even]
        rw [gEval_pair, gStep_node, unpair_pair_fst] at hok
        have hlt1 : Nat.pair a.unpair.1 cert.unpair.2.unpair.2.unpair.1 < Nat.pair (2 * a + 2) cert :=
          pair_lt_pair_of_lt_le (by have := unpair_fst_le a; omega) (unpair_snd_snd_fst_le cert)
        have hlt2 : Nat.pair a.unpair.2 cert.unpair.2.unpair.2.unpair.2 < Nat.pair (2 * a + 2) cert :=
          pair_lt_pair_of_lt_le (by have := unpair_snd_le a; omega) (unpair_snd_snd_snd_le cert)
        rw [listGet_rtbl_gEval fe fU fV mIdx hlt1,
          listGet_rtbl_gEval fe fU fV mIdx hlt2] at hok
        rw [nat_mul_eq_one, nat_mul_eq_one] at hok
        obtain ⟨⟨hokL, hokR⟩, hokV⟩ := hok
        have hgL := ih _ (hw ▸ hlt1) a.unpair.1 cert.unpair.2.unpair.2.unpair.1 rfl hokL
        have hgR := ih _ (hw ▸ hlt2) a.unpair.2 cert.unpair.2.unpair.2.unpair.2 rfl hokR
        rw [gEval_out, gEval_out] at hokV
        refine GRel.node hgL hgR ?_
        exact (hV _ _ cert.unpair.1).mp ⟨cert.unpair.2.unpair.1, hokV⟩
  intro n cert; exact key (Nat.pair n cert) n cert rfl

end Computability
end Exercise717
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap Example61 Exercise510 Proposition77
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

namespace Exercise717


variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}


/-- **Exercise 7.17 (Part 2) (Scott 1981, PRG-19).** If `E` is effectively given (presentation `Q`) and
`u : D → E`, `v : E × E → E` are computable, then the unique strict catamorphism `g : D^§ → E`
(`gMap`) is computable.

The index relation `Xₙ g Yₘ = GRel u v (Vₙ)(Yₘ)` is realised as the recursively-enumerable existential
`∃ cert, gEval⟨n,cert⟩.ok = 1 ∧ Y_{cert.out} = Yₘ` over the primitive-recursive certificate evaluator
`gEval`. Soundness (`gEval_sound`) and completeness (`gEval_complete`) of the certificate give the
equivalence; the deciders `fe`/`fU`/`fV` are read off `Q.eq_computable` and the r.e. relations of
`u`/`v`. -/
theorem gMap_isComputable (hD : ∀ X, D.mem X → X.Nonempty)
    (P : ComputablePresentation D) (Q : ComputablePresentation E)
    (hu : ComputableMap P Q u)
    (hv : ComputableMap (prodPresentation Q Q) Q v) :
    ComputableMap (dsharpPresentation P hD) Q (gMap u v hD) := by
  constructor
  obtain ⟨qU, hqU, hqUe⟩ := hu
  obtain ⟨fU, hfUp, hfUe⟩ := hqU
  obtain ⟨qV, hqV, hqVe⟩ := hv
  obtain ⟨fV, hfVp, hfVe⟩ := hqV
  obtain ⟨fe, hfep, hfee⟩ := Q.eq_computable
  have hMidx : Q.X Q.masterIdx = E.master := Q.masterIdx_spec
  have hEq : ∀ m, fe (Nat.pair m Q.masterIdx) = 1 ↔ Q.X m = E.master := by
    intro m
    have h := hfee (Nat.pair m Q.masterIdx)
    simp only [unpair_pair_fst, unpair_pair_snd] at h
    rw [hMidx] at h; exact h.symm
  have hU : ∀ a m, (∃ i, fU (Nat.pair i (Nat.pair a m)) = 1) ↔ u.rel (P.X a) (Q.X m) := by
    intro a m
    have h := hqUe (Nat.pair a m)
    simp only [unpair_pair_fst, unpair_pair_snd] at h
    rw [h]; exact exists_congr fun i => (hfUe (Nat.pair i (Nat.pair a m))).symm
  have hV : ∀ k1 k2 m, (∃ i, fV (Nat.pair i (Nat.pair (Nat.pair k1 k2) m)) = 1) ↔
      v.rel (prodNbhd (Q.X k1) (Q.X k2)) (Q.X m) := by
    intro k1 k2 m
    have h := hqVe (Nat.pair (Nat.pair k1 k2) m)
    simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd] at h
    rw [h]; exact exists_congr fun i => (hfVe (Nat.pair i (Nat.pair (Nat.pair k1 k2) m))).symm
  -- The certificate body is recursively decidable, hence its existential projection is r.e.
  have hgEval : Nat.Primrec (gEval fe fU fV Q.masterIdx) :=
    primrec_gOf (primrec_gStep fe fU fV Q.masterIdx hfep hfUp hfVp)
  have hidx : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2.unpair.1 s.unpair.1) :=
    (Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left
  have hp1 : RecDecidable (fun s : ℕ =>
      (gEval fe fU fV Q.masterIdx (Nat.pair s.unpair.2.unpair.1 s.unpair.1)).unpair.1 = 1) :=
    ⟨_, Nat.Primrec.left.comp (hgEval.comp hidx), fun _ => Iff.rfl⟩
  have hg2 : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.1.unpair.1 s.unpair.2.unpair.2) :=
    (Nat.Primrec.left.comp Nat.Primrec.left).pair (Nat.Primrec.right.comp Nat.Primrec.right)
  have hp2 : RecDecidable (fun s : ℕ => Q.X s.unpair.1.unpair.1 = Q.X s.unpair.2.unpair.2) :=
    RecDecidable.of_iff (fun s => by simp only [unpair_pair_fst, unpair_pair_snd])
      (Q.eq_computable.comp hg2)
  have hbase : REPred (fun s : ℕ =>
      (gEval fe fU fV Q.masterIdx (Nat.pair s.unpair.2.unpair.1 s.unpair.1)).unpair.1 = 1
        ∧ Q.X s.unpair.1.unpair.1 = Q.X s.unpair.2.unpair.2) := (hp1.and hp2).re
  unfold REPred₂
  refine REPred.of_iff (fun t => ?_) (REPred.proj hbase)
  simp only [unpair_pair_fst, unpair_pair_snd]
  constructor
  · intro hg
    obtain ⟨cert, hok, heq⟩ :=
      gEval_complete fe fU fV Q.masterIdx hD P Q hEq hMidx hU hV t.unpair.1 (Q.X t.unpair.2) hg
    exact ⟨cert, hok, heq⟩
  · rintro ⟨cert, hok, heq⟩
    have hsound := gEval_sound fe fU fV Q.masterIdx P Q hEq hU hV t.unpair.1 cert hok
    rw [heq] at hsound
    exact hsound

end Exercise717
end

end DomainTheory.NeighbourhoodSystems
namespace DomainTheory.NeighbourhoodSystems.Exercise717
section
set_option linter.unusedVariables false

theorem example_717_part2.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {E : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  {u : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β D E}
  {v :
    @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum β β) β (@DomainTheory.NeighbourhoodSystems.prod β β E E) E}
  (hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X)
  (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α D)
  (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β E),
  @DomainTheory.NeighbourhoodSystems.ComputableMap α β D E P Q u →
    @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum β β) β (@DomainTheory.NeighbourhoodSystems.prod β β E E) E
        (@DomainTheory.NeighbourhoodSystems.prodPresentation β β E E Q Q) Q v →
      @DomainTheory.NeighbourhoodSystems.ComputableMap (Prod (List Bool) α) β
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD) E
        (@DomainTheory.NeighbourhoodSystems.Proposition77.dsharpPresentation α D P hD) Q
        (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α β D E u v hD) :=
  @DomainTheory.NeighbourhoodSystems.Exercise717.gMap_isComputable
end

end DomainTheory.NeighbourhoodSystems.Exercise717
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap ApproximableMap₂ Domain.Recursive

namespace NeighborhoodSystem

variable {α : Type*} (V : NeighborhoodSystem α)

end NeighborhoodSystem
end
end DomainTheory.NeighbourhoodSystems
end
