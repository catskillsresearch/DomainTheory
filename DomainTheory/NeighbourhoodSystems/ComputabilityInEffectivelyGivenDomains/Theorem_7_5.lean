module

public import DomainTheory.NeighbourhoodSystems.TypedLambdaCalculus.Table_5_5
public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_12

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/- concordance: source L4361 THEOREM 7.5 function space effective -/
/-- **Theorem 7.5 (existence part) (Scott 1981, PRG-19).** If `𝒟₀` and `𝒟₁` are effectively given,
then so is the function space `(𝒟₀ → 𝒟₁)`. Choice-free. -/
theorem funSpace_isEffectivelyGiven (h₀ : V₀.IsEffectivelyGiven) (h₁ : V₁.IsEffectivelyGiven) :
    (funSpace V₀ V₁).IsEffectivelyGiven := by
  obtain ⟨P₀⟩ := h₀
  obtain ⟨P₁⟩ := h₁
  obtain ⟨incl0, hincl0p, hincl0s⟩ := P₀.incl_computable
  obtain ⟨incl1, hincl1p, hincl1s⟩ := P₁.incl_computable
  obtain ⟨eq1, heq1p, heq1s⟩ := P₁.eq_computable
  obtain ⟨fc0, hfc0p, hfc0s⟩ := P₀.cons_computable
  obtain ⟨fc1, hfc1p, hfc1s⟩ := P₁.cons_computable
  exact ⟨funPresentation P₀ P₁ (funConsChar P₀ P₁ fc0 fc1) incl0 incl1 eq1
    (funConsChar_spec P₀ P₁ fc0 fc1 (fun s => (hfc0s s).symm) (fun s => (hfc1s s).symm))
    (primrec_funConsChar P₀ P₁ fc0 fc1 hfc0p hfc1p)
    (fun s => (hincl0s s).symm) hincl0p
    (fun s => (hincl1s s).symm) hincl1p
    (fun s => (heq1s s).symm) heq1p⟩

/-- **The step neighbourhood `[X₀ⱼ, Y₁ₘ]` as a one-entry `Xenum`.** The code `⟨⟨j, m⟩, 0⟩ + 1`
decodes to the singleton entry-list `[⟨j, m⟩]`, which is always consistent (the step map itself is a
witness), so `Xenum` of it is `stepFun [(X₀ⱼ, Y₁ₘ)] = [X₀ⱼ, Y₁ₘ]`. -/
theorem Xenum_singleton (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (j m : ℕ) :
    Xenum P₀ P₁ gN (Nat.pair (Nat.pair j m) 0 + 1) = step (P₀.X j) (P₁.X m) := by
  have hfp : funPair P₀ P₁ (Nat.pair j m) = (P₀.X j, P₁.X m) := by
    show (P₀.X (Nat.pair j m).unpair.1, P₁.X (Nat.pair j m).unpair.2) = (P₀.X j, P₁.X m)
    rw [unpair_pair_fst, unpair_pair_snd]
  have hdec : decodeList (Nat.pair (Nat.pair j m) 0 + 1) = [Nat.pair j m] := by
    rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
  have hstepeq : (stepFun (funListOf P₀ P₁ [Nat.pair j m]) : Set (ApproximableMap V₀ V₁))
      = step (P₀.X j) (P₁.X m) := by
    show stepFun [funPair P₀ P₁ (Nat.pair j m)] = step (P₀.X j) (P₁.X m)
    rw [hfp, stepFun_singleton]
  have hcons : gN (Nat.pair (Nat.pair j m) 0 + 1) = 1 := by
    rw [hgN, hdec, hstepeq]; exact (step_mem (P₀.mem_X j) (P₁.mem_X m)).2
  rw [Xenum_pos P₀ P₁ hcons, hdec, hstepeq]

section ConsChain

variable {V : NeighborhoodSystem α} (P : ComputablePresentation V)


/-- **Consistency via the `inter`-chain (choice-free).** A finite index set `js` is consistent — i.e.
`⋂{X_j ∣ j ∈ js}` is a neighbourhood — exactly when the always-a-neighbourhood `X_{idxchain js}` sits
inside every `X_j` (`j ∈ js`). -/
theorem consChain_iff (js : List ℕ) :
    (∀ j ∈ js, P.X (idxchain P js) ⊆ P.X j) ↔ V.mem (interFrom P V.master js) := by
  constructor
  · intro hle
    have hsub : P.X (idxchain P js) ⊆ interFrom P V.master js := by
      intro z hz
      rw [mem_interFrom]
      exact ⟨V.sub_master (P.mem_X _) hz, fun j hj => hle j hj hz⟩
    exact interFrom_mem_of_witness P (P.mem_X _) hsub V.master_mem
  · intro hmem j hj
    rw [idxchain_spec P hmem]
    exact fun z hz => (mem_interFrom P |>.mp hz).2 j hj

end ConsChain

/-- **Evaluation against a product neighbourhood.** `(F, X) eval Y ↔ F ⊆ [X, Y]`, for any
function-space neighbourhood `F` and basic neighbourhoods `X, Y`: every map in `F` relates `X` to `Y`
exactly when `F` is contained in the step set `[X, Y] = {f ∣ f X Y}`. -/
theorem evalMap_rel_prodNbhd_iff {F : Set (ApproximableMap V₀ V₁)} (hF : (funSpace V₀ V₁).mem F)
    {X : Set α} (hX : V₀.mem X) {Y : Set β} (hY : V₁.mem Y) :
    (evalMap V₀ V₁).rel (prodNbhd F X) Y ↔ F ⊆ step X Y := by
  show (prod (funSpace V₀ V₁) V₀).mem (prodNbhd F X) ∧
    (eval V₀ V₁).rel (Sum.inl ⁻¹' prodNbhd F X) (Sum.inr ⁻¹' prodNbhd F X) Y ↔ _
  rw [inl_preimage_prodNbhd, inr_preimage_prodNbhd]
  constructor
  · rintro ⟨_, _, _, _, hrel⟩ f hf; exact mem_step.mpr (hrel f hf)
  · intro hsub
    exact ⟨prod_mem_prodNbhd hF hX, hF, hX, hY, fun f hf => mem_step.mp (hsub hf)⟩

/-- **Theorem 7.5 (Scott 1981, PRG-19) — `eval` is computable (choice-free).** Relative to the
function-space presentation `funPresentation` (and the product/codomain presentations), the
evaluation map `eval : (𝒟₀ → 𝒟₁) × 𝒟₀ → 𝒟₁` is computable: its neighbourhood relation is the
*recursively decidable* function-space inclusion `Xenum c ⊆ [X₀ⱼ, Y₁ₘ]`, hence recursively
enumerable. -/
theorem evalMap_isComputable (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (heq1p : Nat.Primrec eq1) :
    ComputableMap
      (prodPresentation (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
        hincl1 hincl1p heq1 heq1p) P₀) P₁ (evalMap V₀ V₁) := by
  constructor
  -- The function-space inclusion is recursively decidable (`funPresentation.incl_computable`);
  -- `funPresentation.X` is definitionally `Xenum`, so we read it off directly.
  have hsub : RecDecidable (fun s => Xenum P₀ P₁ gN s.unpair.1 ⊆ Xenum P₀ P₁ gN s.unpair.2) :=
    (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
      hincl1 hincl1p heq1 heq1p).incl_computable
  -- Re-index `t ↦ ⟨(t.1).1, ⟨⟨(t.1).2, t.2⟩, 0⟩ + 1⟩`: `Xenum_{(t.1).1} ⊆ [X₀_{(t.1).2}, Y₁_{t.2}]`.
  have h11 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.1) :=
    Nat.Primrec.left.comp Nat.Primrec.left
  have h12 : Nat.Primrec (fun t : ℕ => t.unpair.1.unpair.2) :=
    Nat.Primrec.right.comp Nat.Primrec.left
  have hg : Nat.Primrec (fun t => Nat.pair t.unpair.1.unpair.1
      (Nat.pair (Nat.pair t.unpair.1.unpair.2 t.unpair.2) 0 + 1)) :=
    h11.pair (Nat.Primrec.succ.comp ((h12.pair Nat.Primrec.right).pair (Nat.Primrec.const 0)))
  refine (RecDecidable.of_iff (fun t => ?_) (hsub.comp hg)).re
  simp only [unpair_pair_fst, unpair_pair_snd]
  rw [Xenum_singleton P₀ P₁ gN hgN t.unpair.1.unpair.2 t.unpair.2,
    show (prodPresentation (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
        hincl1 hincl1p heq1 heq1p) P₀).X t.unpair.1
      = prodNbhd (Xenum P₀ P₁ gN t.unpair.1.unpair.1) (P₀.X t.unpair.1.unpair.2) from rfl,
    evalMap_rel_prodNbhd_iff (Xenum_mem P₀ P₁ gN hgN _) (P₀.mem_X _) (P₁.mem_X _)]

theorem funListOf_append (la lb : List ℕ) :
    funListOf P₀ P₁ (la ++ lb) = funListOf P₀ P₁ la ++ funListOf P₀ P₁ lb := by
  simp [funListOf, List.map_append]

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

theorem interList_subset_base {base : Set β} {M : List (Set β)} : interList base M ⊆ base :=
  fun _ hz => (mem_interList.mp hz).1
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
variable (P₀ : ComputablePresentation V₀) (P₁ : ComputablePresentation V₁)

/-- **Bridge.** `φ ∋ Xenum c` iff, *when `c` is consistent*, `φ` contains every constituent step. -/
theorem mem_Xenum_iff (gN : ℕ → ℕ) (φ : (funSpace V₀ V₁).Element) (c : ℕ) :
    φ.mem (Xenum P₀ P₁ gN c) ↔
      (gN c = 1 → ∀ e ∈ decodeList c, φ.mem (step (P₀.X e.unpair.1) (P₁.X e.unpair.2))) := by
  by_cases h : gN c = 1
  · rw [Xenum_pos P₀ P₁ h, mem_stepFun_iff φ (funListOf_valid P₀ P₁ (decodeList c))]
    constructor
    · intro hp _ e he
      exact hp (funPair P₀ P₁ e) (List.mem_map.mpr ⟨e, he, rfl⟩)
    · intro himp p hp
      rw [funListOf, List.mem_map] at hp
      obtain ⟨e, he, rfl⟩ := hp
      exact himp h e he
  · rw [Xenum_neg P₀ P₁ h]
    constructor
    · intro _ hcon; exact absurd hcon h
    · intro _; rw [← funSpace_master]; exact φ.master_mem

/-- **Theorem 7.5 (Scott 1981, PRG-19) — computable elements = computable maps (choice-free).** For
the function-space enumeration `Xenum` built from a consistency char `gN`, an element `φ` has an r.e.
index set iff the corresponding approximable map `toApproxMap φ` is computable. -/
theorem Xenum_isComputableElement_iff (gN : ℕ → ℕ) (hgNp : Nat.Primrec gN)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (φ : (funSpace V₀ V₁).Element) :
    REPred (fun c => φ.mem (Xenum P₀ P₁ gN c)) ↔ ComputableMap P₀ P₁ (toApproxMap φ) := by
  -- `ComputableMap` unfolds (def-eq) to r.e.-ness of `R' s = φ ∋ [X₀_{s.1}, X₁_{s.2}]`.
  have hbridge := mem_Xenum_iff P₀ P₁ gN φ
  constructor
  · -- element computable ⟹ map computable: reindex by the single-step code `pair s 0 + 1`.
    intro helem
    have hc0p : Nat.Primrec (fun s => Nat.pair s 0 + 1) :=
      Nat.Primrec.succ.comp (primrec_id.pair (Nat.Primrec.const 0))
    have key : REPred (fun s => φ.mem (Xenum P₀ P₁ gN (Nat.pair s 0 + 1))) := helem.comp hc0p
    constructor
    show REPred (fun s => φ.mem (step (P₀.X s.unpair.1) (P₁.X s.unpair.2)))
    refine REPred.of_iff (fun s => ?_) key
    have hdec : decodeList (Nat.pair s 0 + 1) = [s] := by
      rw [decodeList_succ, unpair_pair_fst, unpair_pair_snd, decodeList_zero]
    have hcons : gN (Nat.pair s 0 + 1) = 1 := by
      rw [hgN, hdec]
      show (stepFun [(P₀.X s.unpair.1, P₁.X s.unpair.2)]
        : Set (ApproximableMap V₀ V₁)).Nonempty
      rw [stepFun_singleton]
      exact (step_mem (P₀.mem_X _) (P₁.mem_X _)).2
    rw [hbridge (Nat.pair s 0 + 1), hdec]
    constructor
    · intro hRs _ e he; rw [List.mem_singleton] at he; subst he; exact hRs
    · intro h; exact h hcons s (List.mem_singleton.mpr rfl)
  · -- map computable ⟹ element computable: guard the bounded-`∀` by the decidable `gN c = 1`.
    intro hmap
    have hR' : REPred (fun s => φ.mem (step (P₀.X s.unpair.1) (P₁.X s.unpair.2))) := hmap.out
    have hforall : REPred (fun c => ∀ e ∈ decodeList c,
        φ.mem (step (P₀.X e.unpair.1) (P₁.X e.unpair.2))) := hR'.forall_mem_decodeList
    have hne1 : REPred (fun c => ¬ gN c = 1) :=
      ((RecDecidable.natEq hgNp (Nat.Primrec.const 1)).not).re
    refine REPred.of_iff (fun c => ?_) (hne1.or hforall)
    rw [hbridge c]; exact Decidable.imp_iff_not_or

/-- **Theorem 7.5 (Scott 1981, PRG-19), packaged for `funPresentation`.** An element of the
function-space presentation is a computable element iff it is (the filter of) a computable map. -/
theorem isComputableElement_funPresentation_iff (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₀ P₁ (decodeList c))
      : Set (ApproximableMap V₀ V₁)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₀.X s.unpair.1 ⊆ P₀.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₁.X s.unpair.1 = P₁.X s.unpair.2) (heq1p : Nat.Primrec eq1)
    (φ : (funSpace V₀ V₁).Element) :
    ComputableElement (funPresentation P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
        hincl1 hincl1p heq1 heq1p) φ ↔ ComputableMap P₀ P₁ (toApproxMap φ) :=
  ⟨fun h => (Xenum_isComputableElement_iff P₀ P₁ gN hgNp hgN φ).mp h.out,
    fun h => ⟨(Xenum_isComputableElement_iff P₀ P₁ gN hgNp hgN φ).mpr h⟩⟩

/-- **Membership in `Xenum` for a single map.** A map `f` lies in `Xenum c` iff (when `c` is
consistent) it relates every coded step `⟨X₀ᵢ, X₁ⱼ⟩`; junk codes give `univ`. (The single-map analogue
of `mem_Xenum_iff`.) -/
theorem mem_Xenum_iff_map (gN : ℕ → ℕ) (f : ApproximableMap V₀ V₁) (c : ℕ) :
    f ∈ Xenum P₀ P₁ gN c ↔
      (gN c = 1 → ∀ e ∈ decodeList c, f.rel (P₀.X e.unpair.1) (P₁.X e.unpair.2)) := by
  by_cases h : gN c = 1
  · rw [Xenum_pos P₀ P₁ h, mem_stepFun]
    constructor
    · intro hp _ e he
      exact hp (funPair P₀ P₁ e) (List.mem_map.mpr ⟨e, he, rfl⟩)
    · intro himp p hp
      rw [funListOf, List.mem_map] at hp
      obtain ⟨e, he, rfl⟩ := hp
      exact himp h e he
  · rw [Xenum_neg P₀ P₁ h]
    constructor
    · intro _ hcon; exact absurd hcon h
    · intro _; exact Set.mem_univ f

/-- **Bridge for `curry`.** `(X₀ₙ) curry(g) (Xenum c)` iff, *when `c` is consistent*, `g` relates
`X₀ₙ ∪ X₁_{e.1}` to `X₂_{e.2}` for every coded entry `e`. -/
theorem curry_rel_Xenum_iff {V₂ : NeighborhoodSystem γ} (P₂ : ComputablePresentation V₂)
    (gN : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₁ P₂ (decodeList c))
      : Set (ApproximableMap V₁ V₂)).Nonempty)
    (g : ApproximableMap (prod V₀ V₁) V₂) (n c : ℕ) :
    (curry g).rel (P₀.X n) (Xenum P₁ P₂ gN c) ↔
      (gN c = 1 → ∀ e ∈ decodeList c,
        g.rel (prodNbhd (P₀.X n) (P₁.X e.unpair.1)) (P₂.X e.unpair.2)) := by
  rw [curry_rel]
  constructor
  · rintro ⟨hX, _, hmem⟩
    rw [mem_Xenum_iff_map P₁ P₂ gN (gSection g hX) c] at hmem
    intro hc e he
    have hrel := hmem hc e he
    rwa [gSection_rel] at hrel
  · intro himp
    refine ⟨P₀.mem_X n, Xenum_mem P₁ P₂ gN hgN c, ?_⟩
    rw [mem_Xenum_iff_map P₁ P₂ gN (gSection g (P₀.mem_X n)) c]
    intro hc e he
    rw [gSection_rel]
    exact himp hc e he

/-- **Theorem 7.5 (Scott 1981, PRG-19) — `curry` is computable (choice-free).** If `g : 𝒟₀ × 𝒟₁ → 𝒟₂`
is computable then so is `curry g : 𝒟₀ → (𝒟₁ → 𝒟₂)`: its neighbourhood relation is the parameterised
bounded `∀` (`REPred.forall_mem_decodeList₂`) over the r.e. relation of `g`, guarded by the decidable
consistency flag. -/
theorem curry_isComputable {V₂ : NeighborhoodSystem γ} (P₂ : ComputablePresentation V₂)
    (gN incl0 incl1 eq1 : ℕ → ℕ)
    (hgN : ∀ c, gN c = 1 ↔ (stepFun (funListOf P₁ P₂ (decodeList c))
      : Set (ApproximableMap V₁ V₂)).Nonempty) (hgNp : Nat.Primrec gN)
    (hincl0 : ∀ s, incl0 s = 1 ↔ P₁.X s.unpair.1 ⊆ P₁.X s.unpair.2) (hincl0p : Nat.Primrec incl0)
    (hincl1 : ∀ s, incl1 s = 1 ↔ P₂.X s.unpair.1 ⊆ P₂.X s.unpair.2) (hincl1p : Nat.Primrec incl1)
    (heq1 : ∀ s, eq1 s = 1 ↔ P₂.X s.unpair.1 = P₂.X s.unpair.2) (heq1p : Nat.Primrec eq1)
    {g : ApproximableMap (prod V₀ V₁) V₂}
    (hg : ComputableMap (prodPresentation P₀ P₁) P₂ g) :
    ComputableMap P₀ (funPresentation P₁ P₂ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
      hincl1 hincl1p heq1 heq1p) (curry g) := by
  constructor
  have hg' : REPred (fun s => g.rel ((prodPresentation P₀ P₁).X s.unpair.1) (P₂.X s.unpair.2)) := hg.out
  have hre : Nat.Primrec (fun s => Nat.pair (Nat.pair s.unpair.1 s.unpair.2.unpair.1)
      s.unpair.2.unpair.2) :=
    (Nat.Primrec.left.pair (Nat.Primrec.left.comp Nat.Primrec.right)).pair
      (Nat.Primrec.right.comp Nat.Primrec.right)
  -- `g`'s relation re-indexed to `(n, e) ↦ X₀ₙ ∪ X₁_{e.1} g X₂_{e.2}` is r.e. in `(n, e)`.
  have hS : REPred₂ (fun n e =>
      g.rel (prodNbhd (P₀.X n) (P₁.X e.unpair.1)) (P₂.X e.unpair.2)) := by
    refine REPred.of_iff (fun s => ?_) (hg'.comp hre)
    simp only [prodPresentation_X, unpair_pair_fst, unpair_pair_snd]
  -- bounded `∀` over the coded list, with parameter `n = t.1`
  have hforall : REPred (fun t => ∀ e ∈ decodeList t.unpair.2,
      g.rel (prodNbhd (P₀.X t.unpair.1) (P₁.X e.unpair.1)) (P₂.X e.unpair.2)) :=
    REPred.forall_mem_decodeList₂ hS
  have hne1 : REPred (fun t => ¬ gN t.unpair.2 = 1) :=
    ((RecDecidable.natEq (hgNp.comp Nat.Primrec.right) (Nat.Primrec.const 1)).not).re
  refine REPred.of_iff (fun t => ?_) (hne1.or hforall)
  show (curry g).rel (P₀.X t.unpair.1) (Xenum P₁ P₂ gN t.unpair.2) ↔ _
  rw [curry_rel_Xenum_iff P₀ P₁ P₂ gN hgN g t.unpair.1 t.unpair.2]
  exact Decidable.imp_iff_not_or

end

section
set_option linter.unusedVariables false

theorem theorem_75.{u_1, u_2, u_3} : And
  (And
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN : Nat → Nat),
          Nat.Primrec gN →
            (∀ (c : Nat),
                Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁
                        (Domain.Recursive.decodeList c))))) →
              ∀
                (φ :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
                Iff
                  (Domain.Recursive.REPred fun (c : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) φ
                      (@DomainTheory.NeighbourhoodSystems.Xenum α β V₀ V₁ P₀ P₁ gN c))
                  (@DomainTheory.NeighbourhoodSystems.ComputableMap α β V₀ V₁ P₀ P₁
                    (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ)))
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂) (gN incl0 incl1 eq1 : Nat → Nat)
        (hgN :
          ∀ (c : Nat),
            Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.stepFun β γ V₁ V₂
                  (@DomainTheory.NeighbourhoodSystems.funListOf β γ V₁ V₂ P₁ P₂ (Domain.Recursive.decodeList c)))))
        (hgNp : Nat.Primrec gN)
        (hincl0 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set β) (@Set.instLE β)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl0p : Nat.Primrec incl0)
        (hincl1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set γ) (@Set.instLE γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl1p : Nat.Primrec incl1)
        (heq1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq (Set γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (heq1p : Nat.Primrec eq1)
        {g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂},
        @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
            (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂ g →
          @DomainTheory.NeighbourhoodSystems.ComputableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) P₀
            (@DomainTheory.NeighbourhoodSystems.funPresentation β γ V₁ V₂ P₁ P₂ gN incl0 incl1 eq1 hgN hgNp hincl0
              hincl0p hincl1 hincl1p heq1 heq1p)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN incl0 incl1 eq1 : Nat → Nat)
      (hgN :
        ∀ (c : Nat),
          Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁ (Domain.Recursive.decodeList c)))))
      (hgNp : Nat.Primrec gN)
      (hincl0 :
        ∀ (s : Nat),
          Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le (Set α) (@Set.instLE α)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (hincl0p : Nat.Primrec incl0)
      (hincl1 :
        ∀ (s : Nat),
          Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le (Set β) (@Set.instLE β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (hincl1p : Nat.Primrec incl1)
      (heq1 :
        ∀ (s : Nat),
          Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq (Set β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (heq1p : Nat.Primrec eq1),
      @DomainTheory.NeighbourhoodSystems.ComputableMap
        (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β
        (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
        V₁
        (@DomainTheory.NeighbourhoodSystems.prodPresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀
          (@DomainTheory.NeighbourhoodSystems.funPresentation α β V₀ V₁ P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
            hincl1 hincl1p heq1 heq1p)
          P₀)
        P₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN incl0 incl1 eq1 : Nat → Nat)
    (hgN :
      ∀ (c : Nat),
        Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁ (Domain.Recursive.decodeList c)))))
    (hgNp : Nat.Primrec gN)
    (hincl0 :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set α) (@Set.instLE α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hincl0p : Nat.Primrec incl0)
    (hincl1 :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set β) (@Set.instLE β)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hincl1p : Nat.Primrec incl1)
    (heq1 :
      ∀ (s : Nat),
        Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq (Set β)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
    (heq1p : Nat.Primrec eq1)
    (φ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
    Iff
      (@DomainTheory.NeighbourhoodSystems.ComputableElement
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funPresentation α β V₀ V₁ P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
          hincl1 hincl1p heq1 heq1p)
        φ)
      (@DomainTheory.NeighbourhoodSystems.ComputableMap α β V₀ V₁ P₀ P₁
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ))) :=
  @And.intro
  (And
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN : Nat → Nat),
          Nat.Primrec gN →
            (∀ (c : Nat),
                Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁
                        (Domain.Recursive.decodeList c))))) →
              ∀
                (φ :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
                Iff
                  (Domain.Recursive.REPred fun (c : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) φ
                      (@DomainTheory.NeighbourhoodSystems.Xenum α β V₀ V₁ P₀ P₁ gN c))
                  (@DomainTheory.NeighbourhoodSystems.ComputableMap α β V₀ V₁ P₀ P₁
                    (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ)))
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂) (gN incl0 incl1 eq1 : Nat → Nat)
        (hgN :
          ∀ (c : Nat),
            Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.stepFun β γ V₁ V₂
                  (@DomainTheory.NeighbourhoodSystems.funListOf β γ V₁ V₂ P₁ P₂ (Domain.Recursive.decodeList c)))))
        (hgNp : Nat.Primrec gN)
        (hincl0 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set β) (@Set.instLE β)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl0p : Nat.Primrec incl0)
        (hincl1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set γ) (@Set.instLE γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl1p : Nat.Primrec incl1)
        (heq1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq (Set γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (heq1p : Nat.Primrec eq1)
        {g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂},
        @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
            (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂ g →
          @DomainTheory.NeighbourhoodSystems.ComputableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) P₀
            (@DomainTheory.NeighbourhoodSystems.funPresentation β γ V₁ V₂ P₁ P₂ gN incl0 incl1 eq1 hgN hgNp hincl0
              hincl0p hincl1 hincl1p heq1 heq1p)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN incl0 incl1 eq1 : Nat → Nat)
      (hgN :
        ∀ (c : Nat),
          Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁ (Domain.Recursive.decodeList c)))))
      (hgNp : Nat.Primrec gN)
      (hincl0 :
        ∀ (s : Nat),
          Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le (Set α) (@Set.instLE α)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (hincl0p : Nat.Primrec incl0)
      (hincl1 :
        ∀ (s : Nat),
          Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le (Set β) (@Set.instLE β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (hincl1p : Nat.Primrec incl1)
      (heq1 :
        ∀ (s : Nat),
          Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq (Set β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (heq1p : Nat.Primrec eq1),
      @DomainTheory.NeighbourhoodSystems.ComputableMap
        (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β
        (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
        V₁
        (@DomainTheory.NeighbourhoodSystems.prodPresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀
          (@DomainTheory.NeighbourhoodSystems.funPresentation α β V₀ V₁ P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
            hincl1 hincl1p heq1 heq1p)
          P₀)
        P₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁)))
  (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
    (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN incl0 incl1 eq1 : Nat → Nat)
    (hgN :
      ∀ (c : Nat),
        Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
            (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
              (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁ (Domain.Recursive.decodeList c)))))
    (hgNp : Nat.Primrec gN)
    (hincl0 :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set α) (@Set.instLE α)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hincl0p : Nat.Primrec incl0)
    (hincl1 :
      ∀ (s : Nat),
        Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@LE.le (Set β) (@Set.instLE β)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
    (hincl1p : Nat.Primrec incl1)
    (heq1 :
      ∀ (s : Nat),
        Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
          (@Eq (Set β)
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
            (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
    (heq1p : Nat.Primrec eq1)
    (φ :
      @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
    Iff
      (@DomainTheory.NeighbourhoodSystems.ComputableElement
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)
        (@DomainTheory.NeighbourhoodSystems.funPresentation α β V₀ V₁ P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
          hincl1 hincl1p heq1 heq1p)
        φ)
      (@DomainTheory.NeighbourhoodSystems.ComputableMap α β V₀ V₁ P₀ P₁
        (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ)))
  (@And.intro
    (And
      (And
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN : Nat → Nat),
          Nat.Primrec gN →
            (∀ (c : Nat),
                Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁
                        (Domain.Recursive.decodeList c))))) →
              ∀
                (φ :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
                Iff
                  (Domain.Recursive.REPred fun (c : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) φ
                      (@DomainTheory.NeighbourhoodSystems.Xenum α β V₀ V₁ P₀ P₁ gN c))
                  (@DomainTheory.NeighbourhoodSystems.ComputableMap α β V₀ V₁ P₀ P₁
                    (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ)))
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂) (gN incl0 incl1 eq1 : Nat → Nat)
        (hgN :
          ∀ (c : Nat),
            Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.stepFun β γ V₁ V₂
                  (@DomainTheory.NeighbourhoodSystems.funListOf β γ V₁ V₂ P₁ P₂ (Domain.Recursive.decodeList c)))))
        (hgNp : Nat.Primrec gN)
        (hincl0 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set β) (@Set.instLE β)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl0p : Nat.Primrec incl0)
        (hincl1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set γ) (@Set.instLE γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl1p : Nat.Primrec incl1)
        (heq1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq (Set γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (heq1p : Nat.Primrec eq1)
        {g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂},
        @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
            (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂ g →
          @DomainTheory.NeighbourhoodSystems.ComputableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) P₀
            (@DomainTheory.NeighbourhoodSystems.funPresentation β γ V₁ V₂ P₁ P₂ gN incl0 incl1 eq1 hgN hgNp hincl0
              hincl0p hincl1 hincl1p heq1 heq1p)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g)))
    (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
      (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN incl0 incl1 eq1 : Nat → Nat)
      (hgN :
        ∀ (c : Nat),
          Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
              (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁ (Domain.Recursive.decodeList c)))))
      (hgNp : Nat.Primrec gN)
      (hincl0 :
        ∀ (s : Nat),
          Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le (Set α) (@Set.instLE α)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V₀ P₀ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (hincl0p : Nat.Primrec incl0)
      (hincl1 :
        ∀ (s : Nat),
          Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@LE.le (Set β) (@Set.instLE β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (hincl1p : Nat.Primrec incl1)
      (heq1 :
        ∀ (s : Nat),
          Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
            (@Eq (Set β)
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
              (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.snd Nat Nat (Nat.unpair s)))))
      (heq1p : Nat.Primrec eq1),
      @DomainTheory.NeighbourhoodSystems.ComputableMap
        (Sum (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α) β
        (@DomainTheory.NeighbourhoodSystems.prod (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀)
        V₁
        (@DomainTheory.NeighbourhoodSystems.prodPresentation
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁) α
          (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) V₀
          (@DomainTheory.NeighbourhoodSystems.funPresentation α β V₀ V₁ P₀ P₁ gN incl0 incl1 eq1 hgN hgNp hincl0 hincl0p
            hincl1 hincl1p heq1 heq1p)
          P₀)
        P₁ (@DomainTheory.NeighbourhoodSystems.evalMap α β V₀ V₁))
    (@And.intro
      (And
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN : Nat → Nat),
          Nat.Primrec gN →
            (∀ (c : Nat),
                Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁
                        (Domain.Recursive.decodeList c))))) →
              ∀
                (φ :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
                Iff
                  (Domain.Recursive.REPred fun (c : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) φ
                      (@DomainTheory.NeighbourhoodSystems.Xenum α β V₀ V₁ P₀ P₁ gN c))
                  (@DomainTheory.NeighbourhoodSystems.ComputableMap α β V₀ V₁ P₀ P₁
                    (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ)))
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)))
      (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
        (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁)
        {V₂ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
        (P₂ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation γ V₂) (gN incl0 incl1 eq1 : Nat → Nat)
        (hgN :
          ∀ (c : Nat),
            Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂)
                (@DomainTheory.NeighbourhoodSystems.stepFun β γ V₁ V₂
                  (@DomainTheory.NeighbourhoodSystems.funListOf β γ V₁ V₂ P₁ P₂ (Domain.Recursive.decodeList c)))))
        (hgNp : Nat.Primrec gN)
        (hincl0 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl0 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set β) (@Set.instLE β)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β V₁ P₁
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl0p : Nat.Primrec incl0)
        (hincl1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (incl1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@LE.le (Set γ) (@Set.instLE γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (hincl1p : Nat.Primrec incl1)
        (heq1 :
          ∀ (s : Nat),
            Iff (@Eq Nat (eq1 s) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
              (@Eq (Set γ)
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂ (@Prod.fst Nat Nat (Nat.unpair s)))
                (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X γ V₂ P₂
                  (@Prod.snd Nat Nat (Nat.unpair s)))))
        (heq1p : Nat.Primrec eq1)
        {g :
          @DomainTheory.NeighbourhoodSystems.ApproximableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂},
        @DomainTheory.NeighbourhoodSystems.ComputableMap (Sum α β) γ
            (@DomainTheory.NeighbourhoodSystems.prod α β V₀ V₁) V₂
            (@DomainTheory.NeighbourhoodSystems.prodPresentation α β V₀ V₁ P₀ P₁) P₂ g →
          @DomainTheory.NeighbourhoodSystems.ComputableMap α
            (@DomainTheory.NeighbourhoodSystems.ApproximableMap β γ V₁ V₂) V₀
            (@DomainTheory.NeighbourhoodSystems.funSpace β γ V₁ V₂) P₀
            (@DomainTheory.NeighbourhoodSystems.funPresentation β γ V₁ V₂ P₁ P₂ gN incl0 incl1 eq1 hgN hgNp hincl0
              hincl0p hincl1 hincl1p heq1 heq1p)
            (@DomainTheory.NeighbourhoodSystems.curry α β γ V₀ V₁ V₂ g))
      (@And.intro
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P₀ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V₀)
          (P₁ : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β V₁) (gN : Nat → Nat),
          Nat.Primrec gN →
            (∀ (c : Nat),
                Iff (@Eq Nat (gN c) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                  (@Set.Nonempty (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.stepFun α β V₀ V₁
                      (@DomainTheory.NeighbourhoodSystems.funListOf α β V₀ V₁ P₀ P₁
                        (Domain.Recursive.decodeList c))))) →
              ∀
                (φ :
                  @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                    (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                    (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁)),
                Iff
                  (Domain.Recursive.REPred fun (c : Nat) =>
                    @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element.mem
                      (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                      (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁) φ
                      (@DomainTheory.NeighbourhoodSystems.Xenum α β V₀ V₁ P₀ P₁ gN c))
                  (@DomainTheory.NeighbourhoodSystems.ComputableMap α β V₀ V₁ P₀ P₁
                    (@DomainTheory.NeighbourhoodSystems.toApproxMap α β V₀ V₁ φ)))
        (∀ {α : Type u_1} {β : Type u_2} {V₀ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {V₁ : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β},
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven α V₀ →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven β V₁ →
              @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.IsEffectivelyGiven
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V₀ V₁)
                (@DomainTheory.NeighbourhoodSystems.funSpace α β V₀ V₁))
        @DomainTheory.NeighbourhoodSystems.Xenum_isComputableElement_iff
        @DomainTheory.NeighbourhoodSystems.funSpace_isEffectivelyGiven)
      @DomainTheory.NeighbourhoodSystems.curry_isComputable)
    @DomainTheory.NeighbourhoodSystems.evalMap_isComputable)
  @DomainTheory.NeighbourhoodSystems.isComputableElement_funPresentation_iff
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β γ : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}
  {V₂ : NeighborhoodSystem γ}

/-- The code of the one-entry function-space neighbourhood `[⟨X_{e.1}, X_{e'.1}⟩, X_{e'.2}]` of
`(𝒟₀×𝒟₁→𝒟₂)` (a `Xenum`-singleton over the product presentation). -/
def curryStepCode (a e' : ℕ) : ℕ :=
  Nat.pair (Nat.pair (Nat.pair a e'.unpair.1) e'.unpair.2) 0 + 1

/-- `curryIso V₀ V₁ V₂` sends a filter `x` to the filter of the curried least map (by definition). -/
theorem curryIso_apply (x : (funSpace (prod V₀ V₁) V₂).Element) :
    curryIso V₀ V₁ V₂ x = toFilter (curry (toApproxMap x)) := rfl

theorem primrec_curryStepCode {a e : ℕ → ℕ} (ha : Nat.Primrec a) (he : Nat.Primrec e) :
    Nat.Primrec (fun w => curryStepCode (a w) (e w)) := by
  have h1 : Nat.Primrec (fun w => (e w).unpair.1) := Nat.Primrec.left.comp he
  have h2 : Nat.Primrec (fun w => (e w).unpair.2) := Nat.Primrec.right.comp he
  refine (Nat.Primrec.succ.comp (((ha.pair h1).pair h2).pair (Nat.Primrec.const 0))).of_eq
    (fun w => ?_)
  rfl

end
end DomainTheory.NeighbourhoodSystems
end
