module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_17

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_10
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_24
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_3
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table_5_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

section
/- concordance: source L5191 EXERCISE 8.21 lists of a projection -/
-- Exercise821/aSharpInner.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **The "inner" recursive extension of `a : U → U` to `U§ → U§`**, satisfying `a§(x§) = (a x)§`
and `a§(⟨y,z⟩) = ⟨a§(y), a§(z)⟩` by `gMap_in`/`gMap_pair` — Scott's fixed-point construction for
`a§`, realized directly by Exercise 7.17 Part 2's catamorphism `gMap`. -/
noncomputable def aSharpInner (a : ApproximableMap U U) :
    ApproximableMap (Dsharp U U_mem_nonempty) (Dsharp U U_mem_nonempty) :=
  gMap ((inSharpMap U_mem_nonempty).comp a) (pairSharpMap U_mem_nonempty) U_mem_nonempty

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {hD : ∀ X, D.mem X → X.Nonempty}
variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

section DsharpFunctor

variable {γ δ ε : Type*} {D₀ : NeighborhoodSystem γ} {D₁ : NeighborhoodSystem δ}
  {D₂ : NeighborhoodSystem ε}

variable (hD₀ : ∀ X, D₀.mem X → X.Nonempty) (hD₁ : ∀ X, D₁.mem X → X.Nonempty)
  {hD₂ : ∀ X, D₂.mem X → X.Nonempty}

/-- **The action of `D ↦ D§` on morphisms.** Recurses `f : D₁ → D₀` through the leaves via `gMap`,
leaving the pairing structure alone — the general form of `aSharpInner` (which specializes this at
`D₀ = D₁ = U`, `f := a`). -/
noncomputable def dsharpMap (f : ApproximableMap D₁ D₀) :
    ApproximableMap (Dsharp D₁ hD₁) (Dsharp D₀ hD₀) :=
  gMap ((inSharpMap hD₀).comp f) (pairSharpMap hD₀) hD₁

theorem dsharpMap_eq (f : ApproximableMap D₁ D₀) :
    dsharpMap hD₀ hD₁ f = gMap ((inSharpMap hD₀).comp f) (pairSharpMap hD₀) hD₁ := rfl

/-- **`aSharpInner` is `dsharpMap` at `D₀ = D₁ = U`, `f := a`.** -/
theorem dsharpMap_self_eq_aSharpInner (a : ApproximableMap U U) :
    dsharpMap U_mem_nonempty U_mem_nonempty a = aSharpInner a := rfl

end DsharpFunctor

end

section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- Forward direction: every `GRel (inSharpMap) (pairSharpMap)`-related pair is an `idMap`-related
pair (`MemS`-membership on both sides plus `⊆`). -/
theorem grel_inSharp_pairSharp_imp_idMap_rel :
    ∀ {W Z}, GRel (inSharpMap hD) (pairSharpMap hD) W Z → MemS D W ∧ MemS D Z ∧ W ⊆ Z := by
  intro W Z h
  induction h with
  | gamma hZ => exact ⟨MemS.gamma, hZ ▸ MemS.gamma, hZ ▸ subset_rfl⟩
  | leaf hrel => exact ⟨MemS.zero hrel.1, hrel.2.1, hrel.2.2⟩
  | @node P Q Z₁ Z₂ Z hP hQ hvrel ihP ihQ =>
      obtain ⟨hPmem, hZ1mem, hPZ1⟩ := ihP
      obtain ⟨hQmem, hZ2mem, hQZ2⟩ := ihQ
      obtain ⟨-, hZmem, A, B, hAmem, hBmem, heq, hsub⟩ := hvrel
      obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
      exact ⟨MemS.pair hPmem hQmem, hZmem, (embPair_subset.mpr ⟨hPZ1, hQZ2⟩).trans hsub⟩
end

section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {hD : ∀ X, D.mem X → X.Nonempty}
variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **`i§ : U§ → U`** (Definition-8.9-style fixed computable projection pair for `U§`). -/
noncomputable def iSharp : ApproximableMap (Dsharp U U_mem_nonempty) U :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose

/-- **`I : (D_a)§ → U`**, transporting `iSharp` through `dsharpMap`'s action on the subsystem
injection `(fixedNbhd_subsystem a).inj : D_a → U`. -/
noncomputable def ISharpComb (a : ApproximableMap U U) :
    ApproximableMap (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)) U :=
  iSharp.comp (dsharpMap U_mem_nonempty (fixedNbhd_mem_nonempty a) (fixedNbhd_subsystem a).inj)

end

section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- Backward direction: every `idMap`-related pair is `GRel (inSharpMap) (pairSharpMap)`-related,
by structural induction on `W`'s `MemS`-derivation (generalizing over `Z`). -/
theorem idMap_rel_imp_grel_inSharp_pairSharp :
    ∀ {W}, MemS D W → ∀ {Z}, MemS D Z → W ⊆ Z → GRel (inSharpMap hD) (pairSharpMap hD) W Z := by
  intro W hW
  induction hW with
  | gamma =>
      intro Z hZ hsub
      have hZeq : Z = Gamma D := Set.Subset.antisymm (memS_subset_gamma hZ) hsub
      subst hZeq
      exact GRel.gamma rfl
  | @zero X hX =>
      intro Z hZ hsub
      exact GRel.leaf ⟨hX, hZ, hsub⟩
  | @pair P Q hP hQ ihP ihQ =>
      intro Z hZ hsub
      exact GRel.node (ihP hP subset_rfl) (ihQ hQ subset_rfl)
        ⟨prod_mem_prodNbhd hP hQ, hZ, P, Q, hP, hQ, rfl, hsub⟩

/-- **`gMap in pair = I_{D§}`**: the catamorphism instantiated at `u := in`, `v := pair` (the tree
algebra's own structure maps) is the identity on `D§`. -/
theorem gMap_inSharp_pairSharp_eq_idMap :
    gMap (inSharpMap hD) (pairSharpMap hD) hD = idMap (Dsharp D hD) := by
  apply le_antisymm
  · rw [ApproximableMap.le_iff]
    intro W Z h
    exact grel_inSharp_pairSharp_imp_idMap_rel h
  · rw [ApproximableMap.le_iff]
    intro W Z h
    exact idMap_rel_imp_grel_inSharp_pairSharp h.1 h.2.1 h.2.2

end

section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {hD : ∀ X, D.mem X → X.Nonempty}
variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

section DsharpFunctor

variable {γ δ ε : Type*} {D₀ : NeighborhoodSystem γ} {D₁ : NeighborhoodSystem δ}
  {D₂ : NeighborhoodSystem ε}

variable (hD₀ : ∀ X, D₀.mem X → X.Nonempty) (hD₁ : ∀ X, D₁.mem X → X.Nonempty)
  {hD₂ : ∀ X, D₂.mem X → X.Nonempty}

/-- **`id§ = id`.** -/
theorem dsharpMap_id : dsharpMap hD₀ hD₀ (idMap D₀) = idMap (Dsharp D₀ hD₀) := by
  rw [dsharpMap_eq, comp_idMap]
  exact gMap_inSharp_pairSharp_eq_idMap

end DsharpFunctor
end

section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- **`x^§|_{↑X} = ↑(0X)`**: `inSharp` sends the principal element `↑X` to the principal element of
the leaf neighbourhood `0X`. -/
theorem inSharp_principal {X : Set α} (hX : D.mem X) :
    inSharp D hD (D.principal hX) = (Dsharp D hD).principal (MemS.zero hX) := by
  rw [← inSharpMap_toElementMap hD]
  apply Element.ext
  intro W
  simp only [mem_principal, ← rel_iff_mem_principal (inSharpMap hD) hX, inSharpMap_rel]
  exact ⟨fun h => h.2, fun h => ⟨hX, h⟩⟩
end

section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {hD : ∀ X, D.mem X → X.Nonempty}
variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **`j§ : U → U§`**. -/
noncomputable def jSharp : ApproximableMap U (Dsharp U U_mem_nonempty) :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose

/-- **`J : U → (D_a)§`**, symmetric to `ISharpComb`, via the subsystem projection
`(fixedNbhd_subsystem a).proj : U → D_a`. -/
noncomputable def JSharpComb (a : ApproximableMap U U) :
    ApproximableMap U (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)) :=
  (dsharpMap (fixedNbhd_mem_nonempty a) U_mem_nonempty (fixedNbhd_subsystem a).proj).comp jSharp

/-- **Scott's operator `a§ : U → U`** (Exercise 8.21), conjugating `aSharpInner a` through the
`U§ ⊴ U` projection pair, exactly as Definition 8.9 builds `a+b`, `a×b`, `a→b`. -/
noncomputable def aSharp (a : ApproximableMap U U) : ApproximableMap U U :=
  iSharp.comp ((aSharpInner a).comp jSharp)

theorem aSharp_eq (a : ApproximableMap U U) :
    aSharp a = iSharp.comp ((aSharpInner a).comp jSharp) := rfl

theorem jSharp_comp_iSharp : jSharp.comp iSharp = idMap _ :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.1

end

section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {hD : ∀ X, D.mem X → X.Nonempty}

/-- **`⟨↑P, ↑Q⟩ = ↑(P∪Q)`** (general, for any two neighbourhood systems): the pairing of two
principal elements is the principal element of the product neighbourhood. -/
theorem pair_principal_eq_principal_prodNbhd {γ δ : Type*} {V₀ : NeighborhoodSystem γ}
    {V₁ : NeighborhoodSystem δ} {P : Set γ} {Q : Set δ} (hP : V₀.mem P) (hQ : V₁.mem Q) :
    pair (V₀.principal hP) (V₁.principal hQ)
      = (prod V₀ V₁).principal (prod_mem_prodNbhd hP hQ) := by
  apply Element.ext
  intro W
  simp only [mem_pair, mem_principal, prod_mem_iff]
  constructor
  · rintro ⟨P', Q', ⟨hP', hPP'⟩, ⟨hQ', hQQ'⟩, rfl⟩
    exact ⟨⟨P', Q', hP', hQ', rfl⟩, prodNbhd_subset_iff.mpr ⟨hPP', hQQ'⟩⟩
  · rintro ⟨⟨P', Q', hP', hQ', rfl⟩, hsub⟩
    obtain ⟨hPP', hQQ'⟩ := prodNbhd_subset_iff.mp hsub
    exact ⟨P', Q', ⟨hP', hPP'⟩, ⟨hQ', hQQ'⟩, rfl⟩

/-- **`⟨↑P, ↑Q⟩^§ = ↑(1P∪2Q)`**: `pairSharp` sends a pair of principal elements to the principal
element of the corresponding node neighbourhood. -/
theorem pairSharp_principal {P Q : Set (List Bool × α)} (hP : MemS D P) (hQ : MemS D Q) :
    pairSharp D hD ((Dsharp D hD).principal hP) ((Dsharp D hD).principal hQ)
      = (Dsharp D hD).principal (MemS.pair hP hQ) := by
  rw [← pairSharpMap_toElementMap hD, pair_principal_eq_principal_prodNbhd hP hQ]
  apply Element.ext
  intro W
  rw [mem_principal, ← rel_iff_mem_principal (pairSharpMap hD) (prod_mem_prodNbhd hP hQ),
    pairSharpMap_rel]
  constructor
  · rintro ⟨-, hW, A, B, hA, hB, heq, hsub⟩
    obtain ⟨rfl, rfl⟩ := prodNbhd_injective heq
    exact ⟨hW, hsub⟩
  · rintro ⟨hW, hsub⟩
    exact ⟨prod_mem_prodNbhd hP hQ, hW, P, Q, hP, hQ, rfl, hsub⟩

end

section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {hD : ∀ X, D.mem X → X.Nonempty}
variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

/-- **Uniqueness of the catamorphism** (Exercise 8.21(b)(1), Scott's own remark "`g` is unique
because the values on finite elements are fixed"). Any *strict* `k : D^§ → E` satisfying `gMap`'s two
defining equations at the *element* level — `k(x^§) = u(x)` and `k(⟨y,z⟩) = v(⟨k(y),k(z)⟩)` — is
literally the catamorphism `gMap u v hD`. Proved by induction on the `MemS`-derivation of the input
neighbourhood, generalizing over the output: the `Γ` case is strictness plus `master_rel`; the leaf
case reads the hypothesis off at the principal element `↑X` via `inSharp_principal` and
`rel_iff_mem_principal`; the node case does the same with `pairSharp_principal`, using the induction
hypotheses to identify the two recursive outputs. -/
theorem gMap_eq_of_satisfies {k : ApproximableMap (Dsharp D hD) E} (hk : IsStrict k)
    (hu : ∀ x : D.Element, k.toElementMap (inSharp D hD x) = u.toElementMap x)
    (hv : ∀ y z : (Dsharp D hD).Element,
      k.toElementMap (pairSharp D hD y z)
        = v.toElementMap (pair (k.toElementMap y) (k.toElementMap z))) :
    k = gMap u v hD := by
  have main : ∀ {W}, MemS D W → ∀ Z, k.rel W Z ↔ GRel u v W Z := by
    intro W hW
    induction hW with
    | gamma =>
        intro Z
        constructor
        · intro h; exact GRel.gamma (hk h)
        · intro h
          have hZ : Z = E.master := gRel_gamma_inv hD h
          subst hZ
          exact k.master_rel
    | @zero X hX =>
        intro Z
        have key := hu (D.principal hX)
        rw [inSharp_principal hX] at key
        constructor
        · intro h
          have h1 := (rel_iff_mem_principal k (MemS.zero hX)).mp h
          rw [key] at h1
          exact GRel.leaf ((rel_iff_mem_principal u hX).mpr h1)
        · intro h
          have h1 := (rel_iff_mem_principal u hX).mp (gRel_embZero_inv hD h)
          rw [← key] at h1
          exact (rel_iff_mem_principal k (MemS.zero hX)).mpr h1
    | @pair P Q hP hQ ihP ihQ =>
        intro Z
        have key := hv ((Dsharp D hD).principal hP) ((Dsharp D hD).principal hQ)
        rw [pairSharp_principal hP hQ] at key
        constructor
        · intro h
          have h1 := (rel_iff_mem_principal k (MemS.pair hP hQ)).mp h
          rw [key] at h1
          obtain ⟨V, hVmem, hVrel⟩ := h1
          obtain ⟨Z1, Z2, hZ1, hZ2, rfl⟩ := hVmem
          have hkZ1 : k.rel P Z1 := (rel_iff_mem_principal k hP).mpr hZ1
          have hkZ2 : k.rel Q Z2 := (rel_iff_mem_principal k hQ).mpr hZ2
          exact GRel.node ((ihP Z1).mp hkZ1) ((ihQ Z2).mp hkZ2) hVrel
        · intro h
          obtain ⟨Z1, Z2, hg1, hg2, hvrel⟩ := gRel_embPair_inv hD h
          have h1 := (rel_iff_mem_principal k hP).mp ((ihP Z1).mpr hg1)
          have h2 := (rel_iff_mem_principal k hQ).mp ((ihQ Z2).mpr hg2)
          have h3 : (v.toElementMap (pair (k.toElementMap ((Dsharp D hD).principal hP))
              (k.toElementMap ((Dsharp D hD).principal hQ)))).mem Z :=
            ⟨prodNbhd Z1 Z2, ⟨Z1, Z2, h1, h2, rfl⟩, hvrel⟩
          rw [← key] at h3
          exact (rel_iff_mem_principal k (MemS.pair hP hQ)).mpr h3
  apply ApproximableMap.ext
  intro W Z
  by_cases hW : MemS D W
  · exact main hW Z
  · exact ⟨fun h => absurd (k.rel_dom h) hW, fun h => absurd (gRel_dom h) hW⟩

section DsharpFunctor

variable {γ δ ε : Type*} {D₀ : NeighborhoodSystem γ} {D₁ : NeighborhoodSystem δ}
  {D₂ : NeighborhoodSystem ε}

variable (hD₀ : ∀ X, D₀.mem X → X.Nonempty) (hD₁ : ∀ X, D₁.mem X → X.Nonempty)
  {hD₂ : ∀ X, D₂.mem X → X.Nonempty}

/-- **`(f' ∘ f)§ = f'§ ∘ f§`.** Applies `gMap_eq_of_satisfies` to `k := (dsharpMap f').comp
(dsharpMap f)`: both defining equations of `k` reduce, via `gMap_in`/`gMap_pair` applied twice, to
the corresponding equation for `dsharpMap (f'.comp f)` — verbatim
`gMap_selfComp_eq_of_isRetraction`'s proof, generalized away from `f' = f` (so no retraction
hypothesis is needed here). -/
theorem dsharpMap_comp (f : ApproximableMap D₂ D₁) (f' : ApproximableMap D₁ D₀) :
    dsharpMap hD₀ hD₂ (f'.comp f) = (dsharpMap hD₀ hD₁ f').comp (dsharpMap hD₁ hD₂ f) := by
  set g1 : ApproximableMap (Dsharp D₂ hD₂) (Dsharp D₁ hD₁) := dsharpMap hD₁ hD₂ f with hg1_def
  set g2 : ApproximableMap (Dsharp D₁ hD₁) (Dsharp D₀ hD₀) := dsharpMap hD₀ hD₁ f' with hg2_def
  symm
  show g2.comp g1 = dsharpMap hD₀ hD₂ (f'.comp f)
  rw [dsharpMap_eq]
  apply gMap_eq_of_satisfies
  · exact isStrict_comp (by rw [hg2_def, dsharpMap_eq]; exact gMap_strict hD₁)
      (by rw [hg1_def, dsharpMap_eq]; exact gMap_strict hD₂)
  · intro x
    have e1 : g1.toElementMap (inSharp D₂ hD₂ x) = inSharp D₁ hD₁ (f.toElementMap x) := by
      rw [hg1_def, dsharpMap_eq, gMap_in hD₂ x, toElementMap_comp, inSharpMap_toElementMap]
    have e2 : g2.toElementMap (inSharp D₁ hD₁ (f.toElementMap x))
        = inSharp D₀ hD₀ (f'.toElementMap (f.toElementMap x)) := by
      rw [hg2_def, dsharpMap_eq, gMap_in hD₁ (f.toElementMap x), toElementMap_comp,
        inSharpMap_toElementMap]
    calc (g2.comp g1).toElementMap (inSharp D₂ hD₂ x)
        = g2.toElementMap (g1.toElementMap (inSharp D₂ hD₂ x)) := toElementMap_comp _ _ _
      _ = g2.toElementMap (inSharp D₁ hD₁ (f.toElementMap x)) := by rw [e1]
      _ = inSharp D₀ hD₀ (f'.toElementMap (f.toElementMap x)) := e2
      _ = ((inSharpMap hD₀).comp (f'.comp f)).toElementMap x := by
          rw [toElementMap_comp, toElementMap_comp, inSharpMap_toElementMap]
  · intro y z
    have e1 : g1.toElementMap (pairSharp D₂ hD₂ y z)
        = pairSharp D₁ hD₁ (g1.toElementMap y) (g1.toElementMap z) := by
      rw [hg1_def, dsharpMap_eq, gMap_pair hD₂ y z, pairSharpMap_toElementMap]
    have e2 : g2.toElementMap (pairSharp D₁ hD₁ (g1.toElementMap y) (g1.toElementMap z))
        = pairSharp D₀ hD₀ (g2.toElementMap (g1.toElementMap y))
          (g2.toElementMap (g1.toElementMap z)) := by
      rw [hg2_def, dsharpMap_eq, gMap_pair hD₁ (g1.toElementMap y) (g1.toElementMap z),
        pairSharpMap_toElementMap]
    calc (g2.comp g1).toElementMap (pairSharp D₂ hD₂ y z)
        = g2.toElementMap (g1.toElementMap (pairSharp D₂ hD₂ y z)) := toElementMap_comp _ _ _
      _ = g2.toElementMap (pairSharp D₁ hD₁ (g1.toElementMap y) (g1.toElementMap z)) := by
          rw [e1]
      _ = pairSharp D₀ hD₀ (g2.toElementMap (g1.toElementMap y))
          (g2.toElementMap (g1.toElementMap z)) := e2
      _ = (pairSharpMap hD₀).toElementMap
          (pair (g2.toElementMap (g1.toElementMap y)) (g2.toElementMap (g1.toElementMap z))) :=
        (pairSharpMap_toElementMap hD₀ _ _).symm
      _ = (pairSharpMap hD₀).toElementMap
          (pair ((g2.comp g1).toElementMap y) ((g2.comp g1).toElementMap z)) := by
        rw [toElementMap_comp, toElementMap_comp]

end DsharpFunctor

/-- **`I ∘ J = a§`**, when `a` is a finitary projection. -/
theorem ISharpComb_comp_JSharpComb {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    (ISharpComb a).comp (JSharpComb a) = aSharp a := by
  unfold ISharpComb JSharpComb
  rw [comp_assoc, ← comp_assoc (dsharpMap _ _ _) (dsharpMap _ _ _) jSharp, ← dsharpMap_comp,
    inj_comp_proj_eq_self ha, dsharpMap_self_eq_aSharpInner]
  exact (aSharp_eq a).symm

/-- **`J ∘ I = I_{(D_a)§}`**, unconditionally (no finitary/projection hypothesis on `a` needed). -/
theorem JSharpComb_comp_ISharpComb (a : ApproximableMap U U) :
    (JSharpComb a).comp (ISharpComb a) =
      idMap (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)) := by
  unfold JSharpComb ISharpComb
  rw [comp_assoc, ← comp_assoc jSharp iSharp (dsharpMap _ _ _), jSharp_comp_iSharp, idMap_comp,
    ← dsharpMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, dsharpMap_id]

/-- **Exercise 8.21(c) (Scott 1981, PRG-19).** For a finitary projection `a` of `U`, the tree
algebra `(D_a)§` of `D_a := fixedNbhd a` is order-isomorphic to `a§`'s own fixed-point domain —
Scott's headline isomorphism `D_{a§} ≅ (D_a)§`. -/
noncomputable def dsharp_fixedNbhd_elementIso {a : ApproximableMap U U}
    (ha : FinitaryProjection a) :
    (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)).Element ≃o
      {y : U.Element // (aSharp a).toElementMap y = y} :=
  elementIsoOfProjectionPair (ISharpComb a) (JSharpComb a) (JSharpComb_comp_ISharpComb a)
    (ISharpComb_comp_JSharpComb ha).symm

/-- **Exercise 8.21(b)(2), general form.** If `a : D → D` is a retraction, so is the recursive
extension `gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD` of `a`'s tree algebra (`aSharpInner a`
specializes this at `D := U`). Applies `gMap_eq_of_satisfies` to `k := g.comp g` (`g` the catamorphism
itself): both defining equations of `k` reduce, via `gMap_in`/`gMap_pair` applied twice, to the
corresponding equation for `g` composed with `a`'s own idempotence. -/
theorem gMap_selfComp_eq_of_isRetraction {a : ApproximableMap D D} (ha : Retraction a) :
    (gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD).comp
        (gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD)
      = gMap ((inSharpMap hD).comp a) (pairSharpMap hD) hD := by
  set u : ApproximableMap D (Dsharp D hD) := (inSharpMap hD).comp a with hu_def
  set v : ApproximableMap (prod (Dsharp D hD) (Dsharp D hD)) (Dsharp D hD) :=
    pairSharpMap hD with hv_def
  set g : ApproximableMap (Dsharp D hD) (Dsharp D hD) := gMap u v hD with hg_def
  have hu_eq : ∀ y : D.Element, u.toElementMap y = inSharp D hD (a.toElementMap y) := by
    intro y; rw [hu_def, toElementMap_comp, inSharpMap_toElementMap]
  show g.comp g = g
  apply gMap_eq_of_satisfies
  · rw [hg_def]; exact isStrict_comp (gMap_strict hD) (gMap_strict hD)
  · intro x
    have e1 : g.toElementMap (inSharp D hD x) = u.toElementMap x := by
      rw [hg_def]; exact gMap_in hD x
    have e2 : g.toElementMap (u.toElementMap x) = u.toElementMap (a.toElementMap x) := by
      rw [hu_eq x, hg_def]; exact gMap_in hD (a.toElementMap x)
    calc (g.comp g).toElementMap (inSharp D hD x)
        = g.toElementMap (g.toElementMap (inSharp D hD x)) := toElementMap_comp _ _ _
      _ = g.toElementMap (u.toElementMap x) := by rw [e1]
      _ = u.toElementMap (a.toElementMap x) := e2
      _ = inSharp D hD (a.toElementMap (a.toElementMap x)) := hu_eq _
      _ = inSharp D hD (a.toElementMap x) := by rw [toElementMap_idem_of_isRetraction ha]
      _ = u.toElementMap x := (hu_eq x).symm
  · intro y z
    have e1 : g.toElementMap (pairSharp D hD y z)
        = v.toElementMap (pair (g.toElementMap y) (g.toElementMap z)) := by
      rw [hg_def]; exact gMap_pair hD y z
    have e2 : v.toElementMap (pair (g.toElementMap y) (g.toElementMap z))
        = pairSharp D hD (g.toElementMap y) (g.toElementMap z) := by
      rw [hv_def]; exact pairSharpMap_toElementMap hD _ _
    have e3 : g.toElementMap (pairSharp D hD (g.toElementMap y) (g.toElementMap z))
        = v.toElementMap
            (pair (g.toElementMap (g.toElementMap y)) (g.toElementMap (g.toElementMap z))) := by
      rw [hg_def]; exact gMap_pair hD _ _
    calc (g.comp g).toElementMap (pairSharp D hD y z)
        = g.toElementMap (g.toElementMap (pairSharp D hD y z)) := toElementMap_comp _ _ _
      _ = g.toElementMap (v.toElementMap (pair (g.toElementMap y) (g.toElementMap z))) := by
          rw [e1]
      _ = g.toElementMap (pairSharp D hD (g.toElementMap y) (g.toElementMap z)) := by rw [e2]
      _ = v.toElementMap
            (pair (g.toElementMap (g.toElementMap y)) (g.toElementMap (g.toElementMap z))) := e3
      _ = v.toElementMap (pair ((g.comp g).toElementMap y) ((g.comp g).toElementMap z)) := by
          rw [toElementMap_comp, toElementMap_comp]

end

section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **`GRel` is monotone in `u`, `v`.** Direct structural induction on the `GRel` derivation,
parallel to `gRel_mono`'s induction on shape. -/
theorem GRel.mono_uv (_hD : ∀ X, D.mem X → X.Nonempty)
    {u u' : ApproximableMap D E} {v v' : ApproximableMap (prod E E) E}
    (hu : u ≤ u') (hv : v ≤ v') :
    ∀ {W Z}, GRel u v W Z → GRel u' v' W Z := by
  intro W Z h
  induction h with
  | gamma hZ => exact GRel.gamma hZ
  | leaf hrel => exact GRel.leaf (hu _ _ hrel)
  | node hP hQ hvrel ihP ihQ => exact GRel.node ihP ihQ (hv _ _ hvrel)
end

section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {hD : ∀ X, D.mem X → X.Nonempty}
variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

theorem aSharpInner_eq (a : ApproximableMap U U) :
    aSharpInner a = gMap ((inSharpMap U_mem_nonempty).comp a) (pairSharpMap U_mem_nonempty)
      U_mem_nonempty := rfl

/-- **Exercise 8.21(b)(2).** If `a` is a retraction (`a∘a = a`), so is its recursive extension
`aSharpInner a`: the specialization of `gMap_selfComp_eq_of_isRetraction` to `D := U`. -/
theorem aSharpInner_idem_of_isRetraction {a : ApproximableMap U U} (ha : Retraction a) :
    Retraction (aSharpInner a) := by
  constructor
  show (aSharpInner a).comp (aSharpInner a) = aSharpInner a
  rw [aSharpInner_eq]
  exact gMap_selfComp_eq_of_isRetraction ha

end

section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

/-- **`gMap` is monotone in `u`, `v`.** -/
theorem gMap_mono (hD : ∀ X, D.mem X → X.Nonempty)
    {u u' : ApproximableMap D E} {v v' : ApproximableMap (prod E E) E}
    (hu : u ≤ u') (hv : v ≤ v') : gMap u v hD ≤ gMap u' v' hD := by
  rw [ApproximableMap.le_iff]
  intro W Z h
  exact GRel.mono_uv hD hu hv h
end

section
open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510
variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
variable {hD : ∀ X, D.mem X → X.Nonempty}
variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

theorem iSharp_comp_jSharp_le : iSharp.comp jSharp ≤ idMap U :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.2.1

/-- **`a ≤ I ⟹ a§ ≤ I`** (half of "`a` a projection ⟹ `a§` a projection", Proposition 8.10's
proof recipe transcribed to `§`). -/
theorem aSharp_le_idMap_of_le {a : ApproximableMap U U} (ha : a ≤ idMap U) :
    aSharp a ≤ idMap U := by
  have h1 : (inSharpMap U_mem_nonempty).comp a ≤ inSharpMap U_mem_nonempty := by
    calc (inSharpMap U_mem_nonempty).comp a
        ≤ (inSharpMap U_mem_nonempty).comp (idMap U) := comp_mono_gen le_rfl ha
      _ = inSharpMap U_mem_nonempty := comp_idMap _
  have h2 : aSharpInner a ≤ idMap (Dsharp U U_mem_nonempty) := by
    calc aSharpInner a
        ≤ gMap (inSharpMap U_mem_nonempty) (pairSharpMap U_mem_nonempty) U_mem_nonempty :=
          gMap_mono U_mem_nonempty h1 le_rfl
      _ = idMap (Dsharp U U_mem_nonempty) := gMap_inSharp_pairSharp_eq_idMap
  calc aSharp a = iSharp.comp ((aSharpInner a).comp jSharp) := aSharp_eq a
    _ ≤ iSharp.comp ((idMap (Dsharp U U_mem_nonempty)).comp jSharp) :=
        comp_mono_gen le_rfl (comp_mono_gen h2 le_rfl)
    _ = iSharp.comp jSharp := by rw [idMap_comp]
    _ ≤ idMap U := iSharp_comp_jSharp_le

/-- **`U§ ⊴ U`.** -/
theorem dsharpU_trianglelefteq_U : Dsharp U U_mem_nonempty ⊴ U :=
  trianglelefteq_of_projectionPair iSharp jSharp jSharp_comp_iSharp iSharp_comp_jSharp_le

theorem iSharp_isComputableMap :
    ComputableMap (dsharpPresentation UComputablePresentation U_mem_nonempty)
      UComputablePresentation iSharp :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.2.2.1

/-- **`a§` is finitary whenever `a` is a finitary projection.** -/
theorem isFinitary_aSharp {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    IsFinitary (aSharp a) :=
  isFinitary_of_projectionPair (ISharpComb a) (JSharpComb a) (JSharpComb_comp_ISharpComb a)
    (ISharpComb_comp_JSharpComb ha).symm

theorem jSharp_isComputableMap :
    ComputableMap UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty) jSharp :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.2.2.2

/-- **`a§` is computable whenever `a` is.** -/
theorem aSharp_isComputable {a : ApproximableMap U U}
    (ha : ComputableMap UComputablePresentation UComputablePresentation a) :
    ComputableMap UComputablePresentation UComputablePresentation (aSharp a) := by
  have hu : ComputableMap UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty)
      ((inSharpMap U_mem_nonempty).comp a) :=
    comp_isComputable ha (inSharp_isComputable U_mem_nonempty UComputablePresentation)
  have hInner : ComputableMap (dsharpPresentation UComputablePresentation U_mem_nonempty)
      (dsharpPresentation UComputablePresentation U_mem_nonempty) (aSharpInner a) :=
    gMap_isComputable U_mem_nonempty UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty) hu
      (pairSharp_isComputable U_mem_nonempty UComputablePresentation)
  exact comp_isComputable (comp_isComputable jSharp_isComputableMap hInner) iSharp_isComputableMap

/-- **`a§`, unfolded one step through the `U§ ⊴ U` projection pair.** Mirrors
`Proposition810.lean`'s `toElementMap_prodComb`/`toElementMap_arrowComb` pattern. -/
theorem toElementMap_aSharp (a : ApproximableMap U U) (x : U.Element) :
    (aSharp a).toElementMap x
      = iSharp.toElementMap ((aSharpInner a).toElementMap (jSharp.toElementMap x)) := by
  rw [aSharp_eq]
  simp only [toElementMap_comp]

/-- **Exercise 8.21(b)(3).** Idempotence of `aSharpInner a` transports through the projection pair
`iSharp`/`jSharp` to idempotence of `aSharp a` itself — exactly `Proposition810.lean`'s
`isRetraction_prodComb`/`isRetraction_arrowComb` recipe (`toElementMap_of_comp_eq_idMap` +
`toElementMap_idem_of_isRetraction`), conjugated through `jSharp_comp_iSharp` instead of
`jTimes_comp_iTimes`/`jArrow_comp_iArrow`. -/
theorem isRetraction_aSharp {a : ApproximableMap U U} (ha2 : Retraction (aSharpInner a)) :
    Retraction (aSharp a) := by
  constructor
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_aSharp a ((aSharp a).toElementMap x),
    toElementMap_aSharp a x, toElementMap_of_comp_eq_idMap jSharp_comp_iSharp,
    toElementMap_idem_of_isRetraction ha2]

/-- **Exercise 8.21(b), assembled.** `a` a projection of `U` `⟹` `a§` a projection: the `≤ I` half
is 8.21(a)'s `aSharp_le_idMap_of_le`; the retraction half chains `aSharpInner_idem_of_isRetraction`
(the `gMap`-level idempotence, via the catamorphism-uniqueness lemma `gMap_eq_of_satisfies`) with
`isRetraction_aSharp` (transport through `U§ ⊴ U`). This completes "`a` a projection ⟹ `a§` a
projection" in full, matching `Proposition810.lean`'s `isProjection_sumComb`/`isProjection_prodComb`/
`isProjection_arrowComb`. -/
theorem isProjection_aSharp {a : ApproximableMap U U} (ha : IsProjection a) :
    IsProjection (aSharp a) :=
  ⟨isRetraction_aSharp (aSharpInner_idem_of_isRetraction ha.1), aSharp_le_idMap_of_le ha.2⟩

/-- **Exercise 8.21, in full (Scott 1981, PRG-19).** `a` a finitary projection of `U` `⟹` `a§` is
a finitary projection of `U`, with `D_{a§} ≅ (D_a)§`. -/
theorem isFinitaryProjection_aSharp {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    FinitaryProjection (aSharp a) :=
  ⟨⟨isProjection_aSharp ha.out.1, isFinitary_aSharp ha⟩⟩

end

section
set_option linter.unusedVariables false

theorem example_821.{u_1} : And
  (And
    (And
      (And
        (∀
          {a :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.aSharp a))
        (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X}
          {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D},
          @DomainTheory.NeighbourhoodSystems.Retraction α D a →
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod (List Bool) α) (Prod (List Bool) α)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Prod (List Bool) α) (Prod (List Bool) α)
                (Prod (List Bool) α) (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD))
              (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)))
      (∀
        {a :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.Retraction (Prod (List Bool) Rat)
            (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
            (DomainTheory.NeighbourhoodSystems.aSharpInner a)))
    (∀
      {a :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.aSharp a)))
  (∀
    {a :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U},
    @DomainTheory.NeighbourhoodSystems.Retraction (Prod (List Bool) Rat)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
        (DomainTheory.NeighbourhoodSystems.aSharpInner a) →
      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.aSharp a)) :=
  @And.intro
  (And
    (And
      (And
        (∀
          {a :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.aSharp a))
        (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X}
          {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D},
          @DomainTheory.NeighbourhoodSystems.Retraction α D a →
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod (List Bool) α) (Prod (List Bool) α)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Prod (List Bool) α) (Prod (List Bool) α)
                (Prod (List Bool) α) (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD))
              (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)))
      (∀
        {a :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.Retraction (Prod (List Bool) Rat)
            (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
            (DomainTheory.NeighbourhoodSystems.aSharpInner a)))
    (∀
      {a :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.aSharp a)))
  (∀
    {a :
      @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
        DomainTheory.NeighbourhoodSystems.U},
    @DomainTheory.NeighbourhoodSystems.Retraction (Prod (List Bool) Rat)
        (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
        (DomainTheory.NeighbourhoodSystems.aSharpInner a) →
      @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U
        (DomainTheory.NeighbourhoodSystems.aSharp a))
  (@And.intro
    (And
      (And
        (∀
          {a :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.aSharp a))
        (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X}
          {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D},
          @DomainTheory.NeighbourhoodSystems.Retraction α D a →
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod (List Bool) α) (Prod (List Bool) α)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Prod (List Bool) α) (Prod (List Bool) α)
                (Prod (List Bool) α) (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD))
              (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)))
      (∀
        {a :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.Retraction (Prod (List Bool) Rat)
            (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
            (DomainTheory.NeighbourhoodSystems.aSharpInner a)))
    (∀
      {a :
        @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
          DomainTheory.NeighbourhoodSystems.U},
      @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U a →
        @DomainTheory.NeighbourhoodSystems.IsProjection Rat DomainTheory.NeighbourhoodSystems.U
          (DomainTheory.NeighbourhoodSystems.aSharp a))
    (@And.intro
      (And
        (∀
          {a :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.aSharp a))
        (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X}
          {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D},
          @DomainTheory.NeighbourhoodSystems.Retraction α D a →
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod (List Bool) α) (Prod (List Bool) α)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Prod (List Bool) α) (Prod (List Bool) α)
                (Prod (List Bool) α) (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD))
              (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)))
      (∀
        {a :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
            DomainTheory.NeighbourhoodSystems.U},
        @DomainTheory.NeighbourhoodSystems.Retraction Rat DomainTheory.NeighbourhoodSystems.U a →
          @DomainTheory.NeighbourhoodSystems.Retraction (Prod (List Bool) Rat)
            (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U_mem_nonempty)
            (DomainTheory.NeighbourhoodSystems.aSharpInner a))
      (@And.intro
        (∀
          {a :
            @DomainTheory.NeighbourhoodSystems.ApproximableMap Rat Rat DomainTheory.NeighbourhoodSystems.U
              DomainTheory.NeighbourhoodSystems.U},
          @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U a →
            @DomainTheory.NeighbourhoodSystems.FinitaryProjection Rat DomainTheory.NeighbourhoodSystems.U
              (DomainTheory.NeighbourhoodSystems.aSharp a))
        (∀ {α : Type u_1} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {hD : ∀ (X : Set α), @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α D X → @Set.Nonempty α X}
          {a : @DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D},
          @DomainTheory.NeighbourhoodSystems.Retraction α D a →
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Prod (List Bool) α) (Prod (List Bool) α)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Prod (List Bool) α) (Prod (List Bool) α)
                (Prod (List Bool) α) (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD)
                (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                    (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                    (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD))
              (@DomainTheory.NeighbourhoodSystems.Exercise717.gMap α (Prod (List Bool) α) D
                (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α α (Prod (List Bool) α) D D
                  (@DomainTheory.NeighbourhoodSystems.Example61.Dsharp α D hD)
                  (@DomainTheory.NeighbourhoodSystems.Proposition77.inSharpMap α D hD) a)
                (@DomainTheory.NeighbourhoodSystems.Proposition77.pairSharpMap α D hD) hD))
        @DomainTheory.NeighbourhoodSystems.isFinitaryProjection_aSharp
        @DomainTheory.NeighbourhoodSystems.gMap_selfComp_eq_of_isRetraction)
      @DomainTheory.NeighbourhoodSystems.aSharpInner_idem_of_isRetraction)
    @DomainTheory.NeighbourhoodSystems.isProjection_aSharp)
  @DomainTheory.NeighbourhoodSystems.isRetraction_aSharp
end

section
open NeighborhoodSystem ApproximableMap
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

theorem ofIso_comp_ofIso_symm (e : V₀.Element ≃o V₀'.Element) :
    (ofIso e).comp (ofIso e.symm) = idMap V₀' := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap,
    OrderIso.apply_symm_apply]

theorem funSpaceCongr_hij (e0 : V₀.Element ≃o V₀'.Element) (e1 : V₁.Element ≃o V₁'.Element) :
    (expMap (ofIso e0.symm) (ofIso e1)).comp (expMap (ofIso e0) (ofIso e1.symm)) =
      idMap (funSpace V₀' V₁') := by
  rw [← expMap_comp, ofIso_comp_ofIso_symm, ofIso_comp_ofIso_symm, expMap_id]

theorem ofIso_symm_comp_ofIso (e : V₀.Element ≃o V₀'.Element) :
    (ofIso e.symm).comp (ofIso e) = idMap V₀ := by
  apply ext_of_toElementMap
  intro x
  rw [toElementMap_comp, toElementMap_ofIso, toElementMap_ofIso, toElementMap_idMap,
    OrderIso.symm_apply_apply]

theorem funSpaceCongr_hji (e0 : V₀.Element ≃o V₀'.Element) (e1 : V₁.Element ≃o V₁'.Element) :
    (expMap (ofIso e0) (ofIso e1.symm)).comp (expMap (ofIso e0.symm) (ofIso e1)) =
      idMap (funSpace V₀ V₁) := by
  rw [← expMap_comp, ofIso_symm_comp_ofIso, ofIso_symm_comp_ofIso, expMap_id]

/-- **Two approximable maps that are *exact* (not merely `≤`) mutual inverses give an
order-isomorphism of element types.** The generic upgrade behind `elementIsoOfProjectionPair`
(`Proposition810b.lean`) when the projection-pair equation holds in *both* directions: then the
fixed-point subtype on the codomain side is *everything*, collapsing to a genuine bijection. -/
def orderIsoOfMutualInverse {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}
    (i : ApproximableMap D E) (j : ApproximableMap E D)
    (hji : j.comp i = idMap D) (hij : i.comp j = idMap E) : D.Element ≃o E.Element where
  toFun := i.toElementMap
  invFun := j.toElementMap
  left_inv x := by rw [← toElementMap_comp, hji, toElementMap_idMap]
  right_inv y := by rw [← toElementMap_comp, hij, toElementMap_idMap]
  map_rel_iff' := by
    intro x x'
    show i.toElementMap x ≤ i.toElementMap x' ↔ x ≤ x'
    constructor
    · intro h
      have hm := j.toElementMap_mono h
      rwa [← toElementMap_comp, ← toElementMap_comp, hji, toElementMap_idMap,
        toElementMap_idMap] at hm
    · intro h
      exact i.toElementMap_mono h

/-- **`funSpace` is a congruence for `≃o`.** `𝒟₀ ≃o 𝒟₀'`, `𝒟₁ ≃o 𝒟₁'` `⟹`
`(𝒟₀ → 𝒟₁) ≃o (𝒟₀' → 𝒟₁')`. -/
noncomputable def funSpaceCongrOrderIso (e0 : V₀.Element ≃o V₀'.Element)
    (e1 : V₁.Element ≃o V₁'.Element) :
    (funSpace V₀ V₁).Element ≃o (funSpace V₀' V₁').Element :=
  orderIsoOfMutualInverse (expMap (ofIso e0.symm) (ofIso e1)) (expMap (ofIso e0) (ofIso e1.symm))
    (funSpaceCongr_hji e0 e1) (funSpaceCongr_hij e0 e1)

/-- **Currying (Theorem 3.12), as a domain isomorphism.** `(𝒟₀ × 𝒟₁ → 𝒟₂) ≅ (𝒟₀ → (𝒟₁ → 𝒟₂))`. -/
theorem curry_isomorphic (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    funSpace (prod V₀ V₁) V₂ ≅ᴰ funSpace V₀ (funSpace V₁ V₂) :=
  ⟨curryIso V₀ V₁ V₂⟩

end

section
set_option linter.unusedVariables false

theorem example_825_congr.{u_1, u_2, u_3} : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} (V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α)
  (V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β)
  (V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ),
  @DomainTheory.NeighbourhoodSystems.Isomorphic
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁)
      V₂)
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
      V₀ (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂))
    (@DomainTheory.NeighbourhoodSystems.funSpace (Sum α β) γ (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂)
    (@DomainTheory.NeighbourhoodSystems.funSpace α (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
      (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂)) :=
  @DomainTheory.NeighbourhoodSystems.curry_isomorphic
end

section
open NeighborhoodSystem ApproximableMap
variable {α β γ α' β' : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable {V₀' : NeighborhoodSystem α'} {V₁' : NeighborhoodSystem β'}

/-- **`funSpace` is a congruence for `≅ᴰ`.** `𝒟₀ ≅ᴰ 𝒟₀'`, `𝒟₁ ≅ᴰ 𝒟₁'` `⟹`
`(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀' → 𝒟₁')`. -/
theorem funSpace_congr (h0 : V₀ ≅ᴰ V₀') (h1 : V₁ ≅ᴰ V₁') :
    funSpace V₀ V₁ ≅ᴰ funSpace V₀' V₁' :=
  h0.elim fun e0 => h1.elim fun e1 => ⟨funSpaceCongrOrderIso e0 e1⟩

/-- **`funSpace` congruence, domain slot.** `𝒟₀ ≅ᴰ 𝒟₀'` `⟹` `(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀' → 𝒟₁)`. -/
theorem funSpace_congr_left (h0 : V₀ ≅ᴰ V₀') : funSpace V₀ V₁ ≅ᴰ funSpace V₀' V₁ :=
  funSpace_congr h0 (Isomorphic.refl V₁)

/-- **`funSpace` congruence, codomain slot.** `𝒟₁ ≅ᴰ 𝒟₁'` `⟹` `(𝒟₀ → 𝒟₁) ≅ᴰ (𝒟₀ → 𝒟₁')`. -/
theorem funSpace_congr_right (h1 : V₁ ≅ᴰ V₁') : funSpace V₀ V₁ ≅ᴰ funSpace V₀ V₁' :=
  funSpace_congr (Isomorphic.refl V₀) h1

end

section
open NeighborhoodSystem ApproximableMap
variable {α β : Type*} {D : NeighborhoodSystem α} {V : NeighborhoodSystem β}

/-- **Closing argument, step 1.** `D ≅ D → V` and `V × V ≅ V` imply `D × D ≅ D`. -/
theorem prod_self_isomorphic (hDV : D ≅ᴰ funSpace D V) (hVV : prod V V ≅ᴰ V) :
    prod D D ≅ᴰ D :=
  ((hDV.prod hDV).trans (funProd_isomorphic).symm).trans
    ((funSpace_congr_right hVV).trans hDV.symm)

/-- **Closing argument, step 2 (Exercise 8.25's main equation).** `D ≅ D → V` and `V × V ≅ V`
imply `D ≅ D → D`. -/
theorem funSpace_self_isomorphic (hDV : D ≅ᴰ funSpace D V) (hVV : prod V V ≅ᴰ V) :
    D ≅ᴰ funSpace D D :=
  have hDD : prod D D ≅ᴰ D := prod_self_isomorphic hDV hVV
  have step : funSpace D D ≅ᴰ D :=
    ((funSpace_congr_right hDV).trans (curry_isomorphic D D V).symm).trans
      ((funSpace_congr_left hDD).trans hDV.symm)
  step.symm

end

section
set_option linter.unusedVariables false

theorem example_825_closing.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {D : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
  @DomainTheory.NeighbourhoodSystems.Isomorphic α (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β D V) D
      (@DomainTheory.NeighbourhoodSystems.funSpace α β D V) →
    @DomainTheory.NeighbourhoodSystems.Isomorphic (Sum β β) β (@DomainTheory.NeighbourhoodSystems.prod β β V V) V →
      @DomainTheory.NeighbourhoodSystems.Isomorphic α (@DomainTheory.NeighbourhoodSystems.ApproximableMap α α D D) D
        (@DomainTheory.NeighbourhoodSystems.funSpace α α D D) :=
  @DomainTheory.NeighbourhoodSystems.funSpace_self_isomorphic
end

end DomainTheory.NeighbourhoodSystems
end

