module

public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_13
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_10
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Proposition_3_4
public import DomainTheory.NeighbourhoodSystems.DomainConstructs.Theorem_3_5
public import DomainTheory.NeighbourhoodSystems.MappingsBetweenDomains.Proposition_2_6
public import DomainTheory.NeighbourhoodSystems.DomainsGivenByNeighbourhoods.Factoid_1_5
@[expose] public section

section
/- concordance: source L1571 EXERCISE 3.24 function-space isomorphisms -/
-- Exercise324/funProdEquiv.lean
namespace DomainTheory.NeighbourhoodSystems

open NeighborhoodSystem ApproximableMap

variable {α β γ : Type*}

variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.24(i) (Scott 1981, PRG-19).** The order-isomorphism on approximable maps
`Hom(𝒟₀, 𝒟₁ × 𝒟₂) ≃o Hom(𝒟₀, 𝒟₁) × Hom(𝒟₀, 𝒟₂)`, `h ↦ (p₀ ∘ h, p₁ ∘ h)`. -/
def funProdEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    ApproximableMap V₀ (prod V₁ V₂) ≃o (ApproximableMap V₀ V₁ × ApproximableMap V₀ V₂) where
  toFun h := ((proj₀ V₁ V₂).comp h, (proj₁ V₁ V₂).comp h)
  invFun p := paired p.1 p.2
  left_inv h := paired_proj h
  right_inv p := by
    ext1
    · exact proj₀_comp_paired p.1 p.2
    · exact proj₁_comp_paired p.1 p.2
  map_rel_iff' := by
    intro h h'
    constructor
    · rintro ⟨h0, h1⟩
      rw [← paired_proj h, ← paired_proj h']
      intro Z P hrel
      obtain ⟨hP, hfP, hgP⟩ := hrel
      exact ⟨hP, h0 _ _ hfP, h1 _ _ hgP⟩
    · intro hle
      refine ⟨fun X Y hrel => ?_, fun X Y hrel => ?_⟩
      · obtain ⟨W, hW, hYW⟩ := hrel
        exact ⟨W, hle X W hW, hYW⟩
      · obtain ⟨W, hW, hYW⟩ := hrel
        exact ⟨W, hle X W hW, hYW⟩

end DomainTheory.NeighbourhoodSystems
end

section
namespace DomainTheory.NeighbourhoodSystems
section

open NeighborhoodSystem ApproximableMap

section
variable {α β γ : Type*}
variable {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β} {V₂ : NeighborhoodSystem γ}

/-- **Exercise 3.24(i) (Scott 1981, PRG-19).** The domain isomorphism
`|𝒟₀ → (𝒟₁ × 𝒟₂)| ≃o |(𝒟₀ → 𝒟₁) × (𝒟₀ → 𝒟₂)|`. -/
def funProdIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β)
    (V₂ : NeighborhoodSystem γ) :
    (funSpace V₀ (prod V₁ V₂)).Element ≃o (prod (funSpace V₀ V₁) (funSpace V₀ V₂)).Element :=
  (funSpaceEquiv V₀ (prod V₁ V₂)).trans <|
    (funProdEquiv V₀ V₁ V₂).trans <|
      (prodCongrOrderIso (funSpaceEquiv V₀ V₁).symm (funSpaceEquiv V₀ V₂).symm).trans
        (prodEquiv (funSpace V₀ V₁) (funSpace V₀ V₂)).symm

/-- **Exercise 3.24(i).** `(𝒟₀ → (𝒟₁ × 𝒟₂)) ≅ (𝒟₀ → 𝒟₁) × (𝒟₀ → 𝒟₂)`. -/
theorem funProd_isomorphic :
    funSpace V₀ (prod V₁ V₂) ≅ᴰ prod (funSpace V₀ V₁) (funSpace V₀ V₂) :=
  ⟨funProdIso V₀ V₁ V₂⟩
end

section
set_option linter.unusedVariables false

theorem example_324.{u_1, u_2, u_3} : ∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
  {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ},
  @DomainTheory.NeighbourhoodSystems.Isomorphic
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α (Sum β γ) V₀
      (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
    (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂))
    (@DomainTheory.NeighbourhoodSystems.funSpace α (Sum β γ) V₀ (@DomainTheory.NeighbourhoodSystems.prod β γ V₁ V₂))
    (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α γ V₀ V₂)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) (@DomainTheory.NeighbourhoodSystems.funSpace α γ V₀ V₂)) :=
  @DomainTheory.NeighbourhoodSystems.funProd_isomorphic
end

section
variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- The `∃/∀`-swap behind `mapOfSeq`: a single input neighbourhood `X ∈ x` works for all coordinates
iff each coordinate has its own (intersect the finitely many non-trivial ones). -/
theorem exists_forall_swap {x : V₀.Element} {W : Set (ℕ × β)}
    {g : ℕ → ApproximableMap V₀ V₁} (hW : (iterSys V₁).mem W) :
    (∃ X, x.mem X ∧ ∀ i, (g i).rel X (fiber W i)) ↔
      (∀ i, ∃ X, x.mem X ∧ (g i).rel X (fiber W i)) := by
  constructor
  · rintro ⟨X, hXx, hall⟩ i; exact ⟨X, hXx, hall i⟩
  · intro hall
    obtain ⟨N, hN⟩ := hW.2
    choose Xs hXx hXrel using hall
    have hbase : x.mem (V₀.interUpTo Xs N) := x.mem_interUpTo Xs (n := N) (fun i _ => hXx i)
    refine ⟨V₀.interUpTo Xs N, hbase, fun i => ?_⟩
    by_cases h : i < N
    · exact (g i).mono (hXrel i) (V₀.interUpTo_subset Xs h) subset_rfl (x.sub hbase)
        ((g i).rel_cod (hXrel i))
    · rw [hN i (not_lt.mp h)]; exact (g i).rel_master (x.sub hbase)

/-- A map `𝒟₀ → 𝒟₁^∞` is detected coordinate-wise: `f ⊑ f'` iff `projₙ ∘ f ⊑ projₙ ∘ f'` for all `n`. -/
theorem le_of_projComp_le {f f' : ApproximableMap V₀ (iterSys V₁)}
    (h : ∀ n, (projN V₁ n).comp f ≤ (projN V₁ n).comp f') : f ≤ f' := by
  rw [le_iff_toElementMap_le]
  intro x
  apply le_of_component_le
  intro n
  have hx := (le_iff_toElementMap_le.mp (h n)) x
  rwa [toElementMap_comp, toElementMap_comp, toElementMap_projN, toElementMap_projN] at hx

/-- The "infinite pairing" map `𝒟₀ → 𝒟₁^∞` of a sequence `g : ℕ → Hom(𝒟₀, 𝒟₁)`:
`X (mapOfSeq g) W ↔ X ∈ 𝒟₀, W ∈ 𝒟₁^∞, and X gᵢ (fiber W i) for all i`. -/
def mapOfSeq (g : ℕ → ApproximableMap V₀ V₁) : ApproximableMap V₀ (iterSys V₁) where
  rel X W := V₀.mem X ∧ (iterSys V₁).mem W ∧ ∀ i, (g i).rel X (fiber W i)
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := ⟨V₀.master_mem, (iterSys V₁).master_mem, fun i => by
    rw [fiber_iterSys_master]; exact (g i).master_rel⟩
  inter_right := by
    rintro X W W' ⟨hX, hW, hrel⟩ ⟨_, hW', hrel'⟩
    refine ⟨hX, ⟨fun i => (g i).rel_cod ((g i).inter_right (hrel i) (hrel' i)), ?_⟩,
      fun i => (g i).inter_right (hrel i) (hrel' i)⟩
    obtain ⟨NW, hNW⟩ := hW.2
    obtain ⟨NW', hNW'⟩ := hW'.2
    refine ⟨max NW NW', fun i hi => ?_⟩
    rw [fiber_inter, hNW i (le_trans (le_max_left _ _) hi),
      hNW' i (le_trans (le_max_right _ _) hi), Set.inter_self]
  mono := by
    rintro X X' W W' ⟨_, _, hrel⟩ hX'X hWW' hX' hW'
    exact ⟨hX', hW', fun i => (g i).mono (hrel i) hX'X (fiber_mono hWW' i) hX' (hW'.1 i)⟩

/-- A pointwise family of order-isomorphisms induces one on the dependent product. -/
def piCongrOrderIso {ι : Type*} {A B : ι → Type*} [∀ i, Preorder (A i)] [∀ i, Preorder (B i)]
    (e : ∀ i, A i ≃o B i) : (∀ i, A i) ≃o (∀ i, B i) where
  toFun f := fun i => e i (f i)
  invFun g := fun i => (e i).symm (g i)
  left_inv f := by funext i; simp
  right_inv g := by funext i; simp
  map_rel_iff' := by
    intro f g
    exact ⟨fun h i => (e i).le_iff_le.mp (h i), fun h i => (e i).le_iff_le.mpr (h i)⟩

/-- `projₙ ∘ f` is monotone in `f`. -/
theorem projComp_mono {f f' : ApproximableMap V₀ (iterSys V₁)} (h : f ≤ f') (n : ℕ) :
    (projN V₁ n).comp f ≤ (projN V₁ n).comp f' := by
  rintro X Y ⟨W, hfXW, hWY⟩
  exact ⟨W, h X W hfXW, hWY⟩

/-- The value of `mapOfSeq g` is the sequence of values `⟨gᵢ(x)⟩`. -/
theorem toElementMap_mapOfSeq (g : ℕ → ApproximableMap V₀ V₁) (x : V₀.Element) :
    (mapOfSeq g).toElementMap x = ofSeq (fun i => (g i).toElementMap x) := by
  apply Element.ext
  intro W
  constructor
  · rintro ⟨X, hXx, _, hW, hrel⟩
    exact ⟨hW, fun i => ⟨X, hXx, hrel i⟩⟩
  · rintro ⟨hW, hfib⟩
    obtain ⟨X, hXx, hrel⟩ := (exists_forall_swap hW).mpr (fun i => hfib i)
    exact ⟨X, hXx, x.sub hXx, hW, hrel⟩

/-- **Exercise 3.24(ii) (Scott 1981, PRG-19).** The order-isomorphism on approximable maps
`Hom(𝒟₀, 𝒟₁^∞) ≃o (ℕ → Hom(𝒟₀, 𝒟₁))`, `f ↦ (n ↦ projₙ ∘ f)`. -/
def funIterEquiv (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    ApproximableMap V₀ (iterSys V₁) ≃o (∀ _ : ℕ, ApproximableMap V₀ V₁) where
  toFun f := fun n => (projN V₁ n).comp f
  invFun g := mapOfSeq g
  left_inv f := by
    apply ext_of_toElementMap
    intro x
    rw [toElementMap_mapOfSeq]
    have hfun : (fun i => ((projN V₁ i).comp f).toElementMap x)
        = (fun i => component (f.toElementMap x) i) := by
      funext i; rw [toElementMap_comp, toElementMap_projN]
    rw [hfun, ofSeq_component]
  right_inv g := by
    funext n
    apply ext_of_toElementMap
    intro x
    rw [toElementMap_comp, toElementMap_mapOfSeq, toElementMap_projN, component_ofSeq]
  map_rel_iff' := by
    intro f f'
    constructor
    · intro h; exact le_of_projComp_le (fun n => h n)
    · intro h n; exact projComp_mono h n

/-- **Exercise 3.24(ii) (Scott 1981, PRG-19).** The domain isomorphism
`|𝒟₀ → 𝒟₁^∞| ≃o |(𝒟₀ → 𝒟₁)^∞|`. -/
def funIterIso (V₀ : NeighborhoodSystem α) (V₁ : NeighborhoodSystem β) :
    (funSpace V₀ (iterSys V₁)).Element ≃o (iterSys (funSpace V₀ V₁)).Element :=
  (funSpaceEquiv V₀ (iterSys V₁)).trans <|
    (funIterEquiv V₀ V₁).trans <|
      (piCongrOrderIso (fun _ : ℕ => (funSpaceEquiv V₀ V₁).symm)).trans
        (iterSeqEquiv (funSpace V₀ V₁)).symm

/-- **Exercise 3.24(ii).** `(𝒟₀ → 𝒟₁^∞) ≅ (𝒟₀ → 𝒟₁)^∞`. -/
theorem funIter_isomorphic : funSpace V₀ (iterSys V₁) ≅ᴰ iterSys (funSpace V₀ V₁) :=
  ⟨funIterIso V₀ V₁⟩
end

section
set_option linter.unusedVariables false

theorem example_324_iter.{u_1, u_2} : ∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
  {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
  @DomainTheory.NeighbourhoodSystems.Isomorphic
    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α (Prod Nat β) V₀
      (@DomainTheory.NeighbourhoodSystems.iterSys β V₁))
    (Prod Nat (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁))
    (@DomainTheory.NeighbourhoodSystems.funSpace α (Prod Nat β) V₀ (@DomainTheory.NeighbourhoodSystems.iterSys β V₁))
    (@DomainTheory.NeighbourhoodSystems.iterSys (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)) :=
  @DomainTheory.NeighbourhoodSystems.funIter_isomorphic
end

end
end DomainTheory.NeighbourhoodSystems
end
