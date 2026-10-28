module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Exercise_7_17

public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Proposition_8_10
public import DomainTheory.NeighbourhoodSystems.RetractsOfTheUniversalDomain.Theorem_8_8

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Exercise_3_24
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_3
public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table_5_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6

@[expose] public section

namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap Example61 Proposition77 Exercise717 Exercise510

variable {α β : Type*} {D : NeighborhoodSystem α} {E : NeighborhoodSystem β}

variable {hD : ∀ X, D.mem X → X.Nonempty}

variable {u : ApproximableMap D E} {v : ApproximableMap (prod E E) E}

noncomputable def aSharpInner (a : ApproximableMap U U) :
    ApproximableMap (Dsharp U U_mem_nonempty) (Dsharp U U_mem_nonempty) :=
  gMap ((inSharpMap U_mem_nonempty).comp a) (pairSharpMap U_mem_nonempty) U_mem_nonempty

section DsharpFunctor

variable {γ δ ε : Type*} {D₀ : NeighborhoodSystem γ} {D₁ : NeighborhoodSystem δ}
  {D₂ : NeighborhoodSystem ε}

variable (hD₀ : ∀ X, D₀.mem X → X.Nonempty) (hD₁ : ∀ X, D₁.mem X → X.Nonempty)
  {hD₂ : ∀ X, D₂.mem X → X.Nonempty}

noncomputable def dsharpMap (f : ApproximableMap D₁ D₀) :
    ApproximableMap (Dsharp D₁ hD₁) (Dsharp D₀ hD₀) :=
  gMap ((inSharpMap hD₀).comp f) (pairSharpMap hD₀) hD₁

theorem dsharpMap_eq (f : ApproximableMap D₁ D₀) :
    dsharpMap hD₀ hD₁ f = gMap ((inSharpMap hD₀).comp f) (pairSharpMap hD₀) hD₁ := rfl

theorem dsharpMap_self_eq_aSharpInner (a : ApproximableMap U U) :
    dsharpMap U_mem_nonempty U_mem_nonempty a = aSharpInner a := rfl

end DsharpFunctor

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

noncomputable def iSharp : ApproximableMap (Dsharp U U_mem_nonempty) U :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose

noncomputable def ISharpComb (a : ApproximableMap U U) :
    ApproximableMap (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)) U :=
  iSharp.comp (dsharpMap U_mem_nonempty (fixedNbhd_mem_nonempty a) (fixedNbhd_subsystem a).inj)

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

theorem gMap_inSharp_pairSharp_eq_idMap :
    gMap (inSharpMap hD) (pairSharpMap hD) hD = idMap (Dsharp D hD) := by
  apply le_antisymm
  · rw [ApproximableMap.le_iff]
    intro W Z h
    exact grel_inSharp_pairSharp_imp_idMap_rel h
  · rw [ApproximableMap.le_iff]
    intro W Z h
    exact idMap_rel_imp_grel_inSharp_pairSharp h.1 h.2.1 h.2.2

section DsharpFunctor

variable {γ δ ε : Type*} {D₀ : NeighborhoodSystem γ} {D₁ : NeighborhoodSystem δ}
  {D₂ : NeighborhoodSystem ε}

variable (hD₀ : ∀ X, D₀.mem X → X.Nonempty) (hD₁ : ∀ X, D₁.mem X → X.Nonempty)
  {hD₂ : ∀ X, D₂.mem X → X.Nonempty}

theorem dsharpMap_id : dsharpMap hD₀ hD₀ (idMap D₀) = idMap (Dsharp D₀ hD₀) := by
  rw [dsharpMap_eq, comp_idMap]
  exact gMap_inSharp_pairSharp_eq_idMap

end DsharpFunctor

theorem inSharp_principal {X : Set α} (hX : D.mem X) :
    inSharp D hD (D.principal hX) = (Dsharp D hD).principal (MemS.zero hX) := by
  rw [← inSharpMap_toElementMap hD]
  apply Element.ext
  intro W
  simp only [mem_principal, ← rel_iff_mem_principal (inSharpMap hD) hX, inSharpMap_rel]
  exact ⟨fun h => h.2, fun h => ⟨hX, h⟩⟩

noncomputable def jSharp : ApproximableMap U (Dsharp U U_mem_nonempty) :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose

noncomputable def JSharpComb (a : ApproximableMap U U) :
    ApproximableMap U (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)) :=
  (dsharpMap (fixedNbhd_mem_nonempty a) U_mem_nonempty (fixedNbhd_subsystem a).proj).comp jSharp

noncomputable def aSharp (a : ApproximableMap U U) : ApproximableMap U U :=
  iSharp.comp ((aSharpInner a).comp jSharp)

namespace aSharp

theorem eq (a : ApproximableMap U U) :
    aSharp a = iSharp.comp ((aSharpInner a).comp jSharp) := rfl

end aSharp

theorem jSharp_comp_iSharp : jSharp.comp iSharp = idMap _ :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.1

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

theorem ISharpComb_comp_JSharpComb {a : ApproximableMap U U} (ha : FinitaryProjection a) :
    (ISharpComb a).comp (JSharpComb a) = aSharp a := by
  unfold ISharpComb JSharpComb
  rw [comp_assoc, ← comp_assoc (dsharpMap _ _ _) (dsharpMap _ _ _) jSharp, ← dsharpMap_comp,
    inj_comp_proj_eq_self ha, dsharpMap_self_eq_aSharpInner]
  exact (aSharp.eq a).symm

theorem JSharpComb_comp_ISharpComb (a : ApproximableMap U U) :
    (JSharpComb a).comp (ISharpComb a) =
      idMap (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)) := by
  unfold JSharpComb ISharpComb
  rw [comp_assoc, ← comp_assoc jSharp iSharp (dsharpMap _ _ _), jSharp_comp_iSharp, idMap_comp,
    ← dsharpMap_comp, (fixedNbhd_subsystem a).proj_comp_inj, dsharpMap_id]

noncomputable def dsharp_fixedNbhd_elementIso {a : ApproximableMap U U}
    (ha : FinitaryProjection a) :
    (Dsharp (fixedNbhd a) (fixedNbhd_mem_nonempty a)).Element ≃o
      {y : U.Element // (aSharp a).toElementMap y = y} :=
  elementIsoOfProjectionPair (ISharpComb a) (JSharpComb a) (JSharpComb_comp_ISharpComb a)
    (ISharpComb_comp_JSharpComb ha).symm

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

theorem GRel.mono_uv (_hD : ∀ X, D.mem X → X.Nonempty)
    {u u' : ApproximableMap D E} {v v' : ApproximableMap (prod E E) E}
    (hu : u ≤ u') (hv : v ≤ v') :
    ∀ {W Z}, GRel u v W Z → GRel u' v' W Z := by
  intro W Z h
  induction h with
  | gamma hZ => exact GRel.gamma hZ
  | leaf hrel => exact GRel.leaf (hu _ _ hrel)
  | node hP hQ hvrel ihP ihQ => exact GRel.node ihP ihQ (hv _ _ hvrel)

theorem aSharpInner_eq (a : ApproximableMap U U) :
    aSharpInner a = gMap ((inSharpMap U_mem_nonempty).comp a) (pairSharpMap U_mem_nonempty)
      U_mem_nonempty := rfl

theorem aSharpInner_idem_of_isRetraction {a : ApproximableMap U U} (ha : Retraction a) :
    Retraction (aSharpInner a) := by
  constructor
  show (aSharpInner a).comp (aSharpInner a) = aSharpInner a
  rw [aSharpInner_eq]
  exact gMap_selfComp_eq_of_isRetraction ha

theorem gMap_mono (hD : ∀ X, D.mem X → X.Nonempty)
    {u u' : ApproximableMap D E} {v v' : ApproximableMap (prod E E) E}
    (hu : u ≤ u') (hv : v ≤ v') : gMap u v hD ≤ gMap u' v' hD := by
  rw [ApproximableMap.le_iff]
  intro W Z h
  exact GRel.mono_uv hD hu hv h

theorem iSharp_comp_jSharp_le : iSharp.comp jSharp ≤ idMap U :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.2.1

theorem dsharpU_trianglelefteq_U : Dsharp U U_mem_nonempty ⊴ U :=
  trianglelefteq_of_projectionPair iSharp jSharp jSharp_comp_iSharp iSharp_comp_jSharp_le

theorem iSharp_isComputableMap :
    ComputableMap (dsharpPresentation UComputablePresentation U_mem_nonempty)
      UComputablePresentation iSharp :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.2.2.1

theorem jSharp_isComputableMap :
    ComputableMap UComputablePresentation
      (dsharpPresentation UComputablePresentation U_mem_nonempty) jSharp :=
  (theorem_8_8_b_strong (dsharpPresentation UComputablePresentation U_mem_nonempty)).choose_spec.choose_spec.2.2.2

end DomainTheory.NeighbourhoodSystems
