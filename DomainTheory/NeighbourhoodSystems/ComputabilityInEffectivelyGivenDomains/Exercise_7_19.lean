module

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Proposition_7_10

public import DomainTheory.NeighbourhoodSystems.ComputabilityInEffectivelyGivenDomains.Definition_7_11

@[expose] public section

section
namespace DomainTheory.NeighbourhoodSystems
section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β γ : Type*}
variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}

/- concordance: source L4663 EXERCISE 7.19 power domain functor -/
/-- **Exercise 7.19 (Scott 1981, PRG-19) — the functorial action `ℙf : ℙD → ℙE`.** Given an
approximable map `f : D → E`, the relation between `ℙD`- and `ℙE`-neighbourhoods is "every member of
the source is `f`-related to some member of the target". This is the representation-independent form
of Scott's displayed `∀ i < n ∃ j < m. Xᵢ f Yⱼ` (see `PFmap_rel_fin`). -/
def PFmap (f : ApproximableMap V W) : ApproximableMap V.PowerDomain W.PowerDomain where
  rel A B := V.PDmem A ∧ W.PDmem B ∧ ∀ X ∈ A, ∃ Y ∈ B, f.rel X Y
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel := by
    refine ⟨V.PDmem_master, W.PDmem_master, ?_⟩
    rintro X ⟨hXmem, hXsub⟩
    exact ⟨W.master, ⟨W.master_mem, subset_rfl⟩,
      f.mono f.master_rel hXsub subset_rfl hXmem W.master_mem⟩
  inter_right := by
    rintro A B B' ⟨hA, hB, hbody⟩ ⟨-, hB', hbody'⟩
    refine ⟨hA, W.PDmem_inter hB hB', ?_⟩
    intro X hX
    obtain ⟨Y, hYB, hrel⟩ := hbody X hX
    obtain ⟨Y', hY'B', hrel'⟩ := hbody' X hX
    have hinmem : W.mem (Y ∩ Y') := f.rel_cod (f.inter_right hrel hrel')
    exact ⟨Y ∩ Y', Set.mem_inter
      (W.PDmem_down hB hYB Set.inter_subset_left hinmem)
      (W.PDmem_down hB' hY'B' Set.inter_subset_right hinmem),
      f.inter_right hrel hrel'⟩
  mono := by
    rintro A A' B B' ⟨_, _, hbody⟩ hA'A hBB' hA' hB'
    refine ⟨hA', hB', ?_⟩
    intro X hX
    obtain ⟨Y, hYB, hrel⟩ := hbody X (hA'A hX)
    exact ⟨Y, hBB' hYB, hrel⟩

@[simp] theorem PFmap_rel {f : ApproximableMap V W} {A : Set (Set α)} {B : Set (Set β)} :
    (PFmap f).rel A B ↔ V.PDmem A ∧ W.PDmem B ∧ ∀ X ∈ A, ∃ Y ∈ B, f.rel X Y := Iff.rfl

/-- **Exercise 7.19 — the combinator `λf. ℙf : (D → E) → (ℙD → ℙE)`.** The flat Smyth-style lift
`(Φ, Ψ) ↦ mem Φ ∧ mem Ψ ∧ ∀ f ∈ Φ, ℙf ∈ Ψ` of Exercise 7.19's functorial action, one level up on the
function spaces (`funSpace`, Theorem 3.10) — the same recipe as Exercise 7.16's `curryComb` and
Exercise 7.21's `papplyEval`. Approximability is immediate: unlike `PFmap` itself, the body is a bare
membership check with no witnesses to gather. -/
def PFmapComb (V : NeighborhoodSystem α) (W : NeighborhoodSystem β) :
    ApproximableMap (funSpace V W) (funSpace V.PowerDomain W.PowerDomain) where
  rel Φ Ψ := (funSpace V W).mem Φ ∧ (funSpace V.PowerDomain W.PowerDomain).mem Ψ ∧
    ∀ f ∈ Φ, PFmap f ∈ Ψ
  rel_dom h := h.1
  rel_cod h := h.2.1
  master_rel :=
    ⟨(funSpace V W).master_mem, (funSpace V.PowerDomain W.PowerDomain).master_mem,
      fun _ _ => Set.mem_univ _⟩
  inter_right := by
    rintro Φ Ψ Ψ' ⟨hΦ, hΨ, hbody⟩ ⟨-, hΨ', hbody'⟩
    obtain ⟨f₀, hf₀⟩ := hΦ.2
    obtain ⟨⟨L₂, hL₂, rfl⟩, -⟩ := hΨ
    obtain ⟨⟨L₂', hL₂', rfl⟩, -⟩ := hΨ'
    refine ⟨hΦ, ⟨⟨L₂ ++ L₂', ?_, (stepFun_append _ _).symm⟩,
        ⟨PFmap f₀, Set.mem_inter (hbody f₀ hf₀) (hbody' f₀ hf₀)⟩⟩,
      fun f hf => Set.mem_inter (hbody f hf) (hbody' f hf)⟩
    intro q hq
    rcases List.mem_append.mp hq with hq' | hq'
    · exact hL₂ q hq'
    · exact hL₂' q hq'
  mono := by
    rintro Φ Φ' Ψ Ψ' ⟨_, _, hbody⟩ hΦ'Φ hΨΨ' hΦ' hΨ'
    exact ⟨hΦ', hΨ', fun f hf => hΨΨ' (hbody f (hΦ'Φ hf))⟩

end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β γ : Type*}

namespace NeighborhoodSystem

variable (V : NeighborhoodSystem α)


end NeighborhoodSystem

variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}


@[simp] theorem PFmapComb_rel {Φ : Set (ApproximableMap V W)}
    {Ψ : Set (ApproximableMap V.PowerDomain W.PowerDomain)} :
    (PFmapComb V W).rel Φ Ψ ↔
      (funSpace V W).mem Φ ∧ (funSpace V.PowerDomain W.PowerDomain).mem Ψ ∧
        ∀ f ∈ Φ, PFmap f ∈ Ψ := Iff.rfl
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β γ : Type*}

namespace NeighborhoodSystem

variable (V : NeighborhoodSystem α)

/-- **Every member of a `ℙ𝒟`-neighbourhood is a `𝒟`-neighbourhood.** -/
theorem PDmem_mem {A : Set (Set α)} (hA : V.PDmem A) {X : Set α} (hX : X ∈ A) : V.mem X := by
  obtain ⟨L, hL, rfl⟩ := hA
  obtain ⟨X', _, hXmem, _⟩ := (V.mem_PDunion).mp hX
  exact hXmem

end NeighborhoodSystem
end

section
open NeighborhoodSystem Domain.Recursive ApproximableMap
variable {α β γ : Type*}
variable {V : NeighborhoodSystem α} {W : NeighborhoodSystem β} {U : NeighborhoodSystem γ}

/-- **Exercise 7.19 — `ℙ` preserves identity maps.** `ℙ(I_D) = I_{ℙD}`. The body
`∀ X ∈ A, ∃ Y ∈ B, X ⊆ Y` is equivalent to `A ⊆ B` by downward closure of `B`. -/
theorem PFmap_idMap (V : NeighborhoodSystem α) : PFmap (idMap V) = idMap V.PowerDomain := by
  apply ApproximableMap.ext
  intro A B
  simp only [PFmap_rel, idMap_rel]
  constructor
  · rintro ⟨hA, hB, hbody⟩
    refine ⟨hA, hB, ?_⟩
    intro X hX
    obtain ⟨Y, hYB, hXmem, _, hXY⟩ := hbody X hX
    exact V.PDmem_down hB hYB hXY hXmem
  · rintro ⟨hA, hB, hsub⟩
    refine ⟨hA, hB, ?_⟩
    intro X hX
    exact ⟨X, hsub hX, V.PDmem_mem hA hX, V.PDmem_mem hA hX, subset_rfl⟩

/-- **Exercise 7.19 — the relation of `ℙf` at the level of `ℙ𝒟`-codes.** Over the canonical
presentations of Proposition 7.10, `(ℙf).rel (Y_c) (Y_d) ↔ ∀ a ∈ dl c, ∃ b ∈ dl d, Xₐ f Y_b`. -/
theorem PFmap_rel_Ypd_iff (P : ComputablePresentation V) (Q : ComputablePresentation W)
    (f : ApproximableMap V W) {c d : ℕ} :
    (PFmap f).rel (V.Ypd P c) (W.Ypd Q d) ↔
      ∀ a ∈ decodeList c, ∃ b ∈ decodeList d, f.rel (P.X a) (Q.X b) := by
  constructor
  · rintro ⟨-, -, hbody⟩ a ha
    have hXin : P.X a ∈ V.Ypd P c := (V.mem_Ypd P).mpr ⟨a, ha, P.mem_X a, subset_rfl⟩
    obtain ⟨Y, hYin, hrel⟩ := hbody (P.X a) hXin
    obtain ⟨b, hb, hYmem, hYsub⟩ := (W.mem_Ypd Q).mp hYin
    exact ⟨b, hb, f.mono hrel subset_rfl hYsub (P.mem_X a) (Q.mem_X b)⟩
  · intro hgen
    refine ⟨V.Ypd_isPDmem P c, W.Ypd_isPDmem Q d, ?_⟩
    rintro X hXin
    obtain ⟨a, ha, hXmem, hXsub⟩ := (V.mem_Ypd P).mp hXin
    obtain ⟨b, hb, hrel⟩ := hgen a ha
    exact ⟨Q.X b, (W.mem_Ypd Q).mpr ⟨b, hb, Q.mem_X b, subset_rfl⟩,
      f.mono hrel hXsub subset_rfl hXmem (Q.mem_X b)⟩

/-- **Exercise 7.19 — Scott's displayed formula.** On generators (finite lists of down-sets)
`(ℙf).rel (⋃_{X∈L₁} ↓X) (⋃_{Y∈L₂} ↓Y) ↔ ∀ X ∈ L₁, ∃ Y ∈ L₂, X f Y`, exactly Scott's
`∀ i < n ∃ j < m. Xᵢ f Yⱼ`. (`→` reads off the generators `Xᵢ`; `←` extends to all members by `mono`
and downward closure of the target.) -/
theorem PFmap_rel_fin (f : ApproximableMap V W) {L₁ : List (Set α)} {L₂ : List (Set β)}
    (hL₁ : ∀ X ∈ L₁, V.mem X) (hL₂ : ∀ Y ∈ L₂, W.mem Y) :
    (PFmap f).rel (⋃ X ∈ L₁, V.upSet X) (⋃ Y ∈ L₂, W.upSet Y)
      ↔ ∀ X ∈ L₁, ∃ Y ∈ L₂, f.rel X Y := by
  constructor
  · rintro ⟨-, -, hbody⟩ X hX
    have hXin : X ∈ ⋃ X' ∈ L₁, V.upSet X' :=
      (V.mem_PDunion).mpr ⟨X, hX, hL₁ X hX, subset_rfl⟩
    obtain ⟨Z, hZin, hrel⟩ := hbody X hXin
    obtain ⟨Y, hY, hZmem, hZsub⟩ := (W.mem_PDunion).mp hZin
    exact ⟨Y, hY, f.mono hrel subset_rfl hZsub (hL₁ X hX) (hL₂ Y hY)⟩
  · intro hgen
    refine ⟨⟨L₁, hL₁, rfl⟩, ⟨L₂, hL₂, rfl⟩, ?_⟩
    rintro Z hZin
    obtain ⟨X, hX, hZmem, hZsub⟩ := (V.mem_PDunion).mp hZin
    obtain ⟨Y, hY, hrel⟩ := hgen X hX
    exact ⟨Y, (W.mem_PDunion).mpr ⟨Y, hY, hL₂ Y hY, subset_rfl⟩,
      f.mono hrel hZsub subset_rfl hZmem (hL₂ Y hY)⟩

/-- **Bounded `∃` over a coded list preserves recursive enumerability.** If `R` is r.e. then so is
`fun d a => ∃ b ∈ decodeList d, R a b`: project out `b` (`REPred.proj`) over the conjunction of the
*recursively decidable* membership `b ∈ decodeList d` with the r.e. body `R a b`. -/
theorem bExists_decodeList_re {R : ℕ → ℕ → Prop} (hR : REPred₂ R) :
    REPred₂ (fun d a => ∃ b ∈ decodeList d, R a b) := by
  have hmem : RecDecidable₂ (fun d b => b ∈ decodeList d) := by
    have heq : RecDecidable₂ (fun e b => e = b) :=
      RecDecidable.natEq Nat.Primrec.left Nat.Primrec.right
    have hbase : RecDecidable₂ (fun d b => ∃ e ∈ decodeList d, e = b) := heq.bExistsList
    refine RecDecidable.of_iff (fun t => ?_) hbase
    constructor
    · intro h; exact ⟨_, h, rfl⟩
    · rintro ⟨e, he, rfl⟩; exact he
  have hpart1 : REPred (fun w : ℕ => w.unpair.1 ∈ decodeList w.unpair.2.unpair.1) := by
    have hg : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.1 w.unpair.1) :=
      (Nat.Primrec.left.comp Nat.Primrec.right).pair Nat.Primrec.left
    refine RecDecidable.re (RecDecidable.of_iff (fun w => ?_) (hmem.comp hg))
    simp only [unpair_pair_fst, unpair_pair_snd]
  have hpart2 : REPred (fun w : ℕ => R w.unpair.2.unpair.2 w.unpair.1) := by
    have hg : Nat.Primrec (fun w : ℕ => Nat.pair w.unpair.2.unpair.2 w.unpair.1) :=
      (Nat.Primrec.right.comp Nat.Primrec.right).pair Nat.Primrec.left
    refine REPred.of_iff (fun w => ?_) (REPred.comp hR hg)
    simp only [unpair_pair_fst, unpair_pair_snd]
  refine REPred.of_iff (fun s => ?_) (hpart1.and hpart2).proj
  simp only [unpair_pair_fst, unpair_pair_snd]

/-- **Exercise 7.19 (Scott's first question) — `ℙf` is computable when `f` is.** Stated at the level
of the `ℙ𝒟`-codes of Proposition 7.10 (`Y_c = ⋃_{a∈dl c} ↓Xₐ`): the relation `(ℙf).rel (Y_c) (Y_d)`
is recursively enumerable in `(c, d)`. -/
theorem PFmap_isComputable_Ypd (P : ComputablePresentation V) (Q : ComputablePresentation W)
    {f : ApproximableMap V W} (hf : ComputableMap P Q f) :
    REPred₂ (fun c d => (PFmap f).rel (V.Ypd P c) (W.Ypd Q d)) := by
  have hR : REPred₂ (fun a b => f.rel (P.X a) (Q.X b)) := hf.out
  have hInner : REPred₂ (fun d a => ∃ b ∈ decodeList d, f.rel (P.X a) (Q.X b)) :=
    bExists_decodeList_re hR
  have hForall := REPred.forall_mem_decodeList₂ hInner
  have hswap : Nat.Primrec (fun s : ℕ => Nat.pair s.unpair.2 s.unpair.1) :=
    Nat.Primrec.right.pair Nat.Primrec.left
  refine REPred.of_iff (fun s => ?_) (hForall.comp hswap)
  simp only [unpair_pair_fst, unpair_pair_snd]
  exact PFmap_rel_Ypd_iff P Q f

/-- **Exercise 7.19 (Scott's first question), packaged.** `ℙf` is a computable map between the
canonical effective presentations `ℙ𝒟`, `ℙℰ` (Proposition 7.10) whenever `f` is computable. -/
theorem PFmap_isComputable (P : ComputablePresentation V) (Q : ComputablePresentation W)
    (consV : ℕ → ℕ) (hconsVp : Nat.Primrec consV)
    (hconsVs : ∀ a b, consV (Nat.pair a b) = 1 ↔ ∃ k, P.X k ⊆ P.X a ∩ P.X b)
    (consW : ℕ → ℕ) (hconsWp : Nat.Primrec consW)
    (hconsWs : ∀ a b, consW (Nat.pair a b) = 1 ↔ ∃ k, Q.X k ⊆ Q.X a ∩ Q.X b)
    {f : ApproximableMap V W} (hf : ComputableMap P Q f) :
    ComputableMap (V.PDPresentation P consV hconsVp hconsVs)
      (W.PDPresentation Q consW hconsWp hconsWs) (PFmap f) := by
  exact ⟨PFmap_isComputable_Ypd P Q hf⟩

/-- Choice-free gathering of composition witnesses along the generators of the source: from a list
`L` of `𝒟`-neighbourhoods each admitting a `(g∘f)`-witness into `C`, build a single list `M` of
`ℰ`-neighbourhoods covering every `X ∈ L` from the `f`-side and covered into `C` from the `g`-side.
Proved by list recursion `obtain`-ing the witnesses (no choice in a `Prop` goal). -/
theorem comp_witness (f : ApproximableMap V W) (g : ApproximableMap W U) (C : Set (Set γ)) :
    ∀ (L : List (Set α)), (∀ X ∈ L, V.mem X) →
      (∀ X ∈ L, ∃ Z, Z ∈ C ∧ ∃ Y, f.rel X Y ∧ g.rel Y Z) →
      ∃ M : List (Set β), (∀ Y ∈ M, W.mem Y) ∧
        (∀ X ∈ L, ∃ Y ∈ M, f.rel X Y) ∧ (∀ Y ∈ M, ∃ Z ∈ C, g.rel Y Z) := by
  intro L
  induction L with
  | nil =>
    intro _ _
    refine ⟨[], ?_, ?_, ?_⟩
    · intro Y hY; cases hY
    · intro X hX; cases hX
    · intro Y hY; cases hY
  | cons X L ih =>
    intro hL hpre
    obtain ⟨Zx, hZxC, Yx, hfx, hgx⟩ := hpre X (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨M, hMmem, hfM, hgM⟩ :=
      ih (fun X' hX' => hL X' (List.mem_cons.mpr (Or.inr hX')))
         (fun X' hX' => hpre X' (List.mem_cons.mpr (Or.inr hX')))
    refine ⟨Yx :: M, ?_, ?_, ?_⟩
    · intro Y hY
      rcases List.mem_cons.mp hY with rfl | hY'
      · exact f.rel_cod hfx
      · exact hMmem Y hY'
    · intro X' hX'
      rcases List.mem_cons.mp hX' with rfl | hX''
      · exact ⟨Yx, List.mem_cons.mpr (Or.inl rfl), hfx⟩
      · obtain ⟨Y, hYM, hrel⟩ := hfM X' hX''
        exact ⟨Y, List.mem_cons.mpr (Or.inr hYM), hrel⟩
    · intro Y hY
      rcases List.mem_cons.mp hY with rfl | hY'
      · exact ⟨Zx, hZxC, hgx⟩
      · exact hgM Y hY'

/-- **Exercise 7.19 — `ℙ` preserves composition.** `ℙ(g ∘ f) = ℙg ∘ ℙf`. The forward direction
constructs the intermediate `ℙE`-neighbourhood from `comp_witness`; the backward direction merely
threads the existential witnesses. -/
theorem PFmap_comp (g : ApproximableMap W U) (f : ApproximableMap V W) :
    PFmap (g.comp f) = (PFmap g).comp (PFmap f) := by
  apply ApproximableMap.ext
  intro A C
  simp only [PFmap_rel, comp_rel]
  constructor
  · rintro ⟨hA, hC, hbody⟩
    obtain ⟨L, hL, rfl⟩ := hA
    have hpre : ∀ X ∈ L, ∃ Z, Z ∈ C ∧ ∃ Y, f.rel X Y ∧ g.rel Y Z := by
      intro X hX
      obtain ⟨Z, hZC, Y, hfXY, hgYZ⟩ :=
        hbody X ((V.mem_PDunion).mpr ⟨X, hX, hL X hX, subset_rfl⟩)
      exact ⟨Z, hZC, Y, hfXY, hgYZ⟩
    obtain ⟨M, hMmem, hfL, hgM⟩ := comp_witness f g C L hL hpre
    refine ⟨⋃ Y ∈ M, W.upSet Y,
      ⟨⟨L, hL, rfl⟩, ⟨M, hMmem, rfl⟩, ?_⟩, ⟨M, hMmem, rfl⟩, hC, ?_⟩
    · intro X hX
      obtain ⟨X', hX', hXmem, hXsub⟩ := (V.mem_PDunion).mp hX
      obtain ⟨Y, hYM, hrel⟩ := hfL X' hX'
      exact ⟨Y, (W.mem_PDunion).mpr ⟨Y, hYM, hMmem Y hYM, subset_rfl⟩,
        f.mono hrel hXsub subset_rfl hXmem (hMmem Y hYM)⟩
    · intro Y hY
      obtain ⟨Y', hY', hYmem, hYsub⟩ := (W.mem_PDunion).mp hY
      obtain ⟨Z, hZC, hrel⟩ := hgM Y' hY'
      exact ⟨Z, hZC, g.mono hrel hYsub subset_rfl hYmem (g.rel_cod hrel)⟩
  · rintro ⟨B, ⟨hA, hB, hfAB⟩, _, hC, hgBC⟩
    refine ⟨hA, hC, ?_⟩
    intro X hX
    obtain ⟨Y, hYB, hfXY⟩ := hfAB X hX
    obtain ⟨Z, hZC, hgYZ⟩ := hgBC Y hYB
    exact ⟨Z, hZC, Y, hfXY, hgYZ⟩

/-- **Choice-free witness gathering (single list).** From `∀ X ∈ L₁, ∃ Y ∈ L₂, f.rel X Y`, build one
list `M` of `(X, Y)` pairs, each drawn from `L₁ × L₂` and `f`-related, that *covers* `L₁`: every
`X ∈ L₁` has a matching `Y` with `(X, Y) ∈ M`. (The one-map analogue of `comp_witness`.) -/
theorem gather_witnesses (f : ApproximableMap V W) :
    ∀ (L₁ : List (Set α)) (L₂ : List (Set β)), (∀ X ∈ L₁, ∃ Y ∈ L₂, f.rel X Y) →
      ∃ M : List (Set α × Set β), (∀ p ∈ M, p.1 ∈ L₁ ∧ p.2 ∈ L₂ ∧ f.rel p.1 p.2) ∧
        ∀ X ∈ L₁, ∃ Y ∈ L₂, (X, Y) ∈ M := by
  intro L₁
  induction L₁ with
  | nil => intro L₂ _; exact ⟨[], by simp, by simp⟩
  | cons X L₁ ih =>
    intro L₂ h
    obtain ⟨Y, hY, hrel⟩ := h X (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨M, hMprop, hMwit⟩ := ih L₂ (fun X' hX' => h X' (List.mem_cons.mpr (Or.inr hX')))
    refine ⟨(X, Y) :: M, ?_, ?_⟩
    · rintro p hp
      rcases List.mem_cons.mp hp with rfl | hp'
      · exact ⟨List.mem_cons.mpr (Or.inl rfl), hY, hrel⟩
      · obtain ⟨hX1, hY1, hrel1⟩ := hMprop p hp'
        exact ⟨List.mem_cons.mpr (Or.inr hX1), hY1, hrel1⟩
    · intro X' hX'
      rcases List.mem_cons.mp hX' with rfl | hX''
      · exact ⟨Y, hY, List.mem_cons.mpr (Or.inl rfl)⟩
      · obtain ⟨Y', hY', hmem⟩ := hMwit X' hX''
        exact ⟨Y', hY', List.mem_cons.mpr (Or.inr hmem)⟩

/-- **Choice-free witness gathering (list of step constraints).** From a finite list `L` of
`ℙD × ℙE`-neighbourhood pairs `(A, B)`, each satisfied by `ℙf` (`(ℙf).rel A B`), build a *single*
finite list `M` of `D × E`-pairs, `f`-related and covering every generator of every `A` in `L`, such
that *any* `g` agreeing with `f` on `M` again satisfies `(ℙg).rel A B` for every `(A, B) ∈ L`. This is
exactly "continuity of `f ↦ ℙf`, unwound to finite data": `M` is the finite portion of `f` that
already forces `ℙf`'s membership in every step-neighbourhood of `L`. -/
theorem exists_stepFun_forall_PFmap_rel (f : ApproximableMap V W) :
    ∀ (L : List (Set (Set α) × Set (Set β))),
      (∀ p ∈ L, V.PDmem p.1 ∧ W.PDmem p.2) → (∀ p ∈ L, (PFmap f).rel p.1 p.2) →
      ∃ M : List (Set α × Set β), (∀ p ∈ M, V.mem p.1 ∧ W.mem p.2) ∧
        (∀ p ∈ M, f.rel p.1 p.2) ∧
        ∀ g : ApproximableMap V W, (∀ p ∈ M, g.rel p.1 p.2) → ∀ p ∈ L, (PFmap g).rel p.1 p.2 := by
  intro L
  induction L with
  | nil => intro _ _; exact ⟨[], by simp, by simp, by simp⟩
  | cons p L ih =>
    intro hL hf
    obtain ⟨hA, hB⟩ := hL p (List.mem_cons.mpr (Or.inl rfl))
    obtain ⟨L₁, hL₁, hAeq⟩ := hA
    obtain ⟨L₂, hL₂, hBeq⟩ := hB
    have hrelAB : (PFmap f).rel p.1 p.2 := hf p (List.mem_cons.mpr (Or.inl rfl))
    rw [hAeq, hBeq] at hrelAB
    have hgen := (PFmap_rel_fin f hL₁ hL₂).mp hrelAB
    obtain ⟨M₀, hM₀prop, hM₀wit⟩ := gather_witnesses f L₁ L₂ hgen
    obtain ⟨M, hMmem, hMrel, hMgen⟩ :=
      ih (fun p' hp' => hL p' (List.mem_cons.mpr (Or.inr hp')))
         (fun p' hp' => hf p' (List.mem_cons.mpr (Or.inr hp')))
    refine ⟨M₀ ++ M, ?_, ?_, ?_⟩
    · intro q hq
      rcases List.mem_append.mp hq with hq' | hq'
      · obtain ⟨hq1, hq2, _⟩ := hM₀prop q hq'
        exact ⟨hL₁ q.1 hq1, hL₂ q.2 hq2⟩
      · exact hMmem q hq'
    · intro q hq
      rcases List.mem_append.mp hq with hq' | hq'
      · exact (hM₀prop q hq').2.2
      · exact hMrel q hq'
    · intro g hg p' hp'
      rcases List.mem_cons.mp hp' with rfl | hp''
      · rw [hAeq, hBeq]
        refine (PFmap_rel_fin g hL₁ hL₂).mpr ?_
        intro X hX
        obtain ⟨Y, hY, hmem⟩ := hM₀wit X hX
        exact ⟨Y, hY, hg (X, Y) (List.mem_append.mpr (Or.inl hmem))⟩
      · exact hMgen g (fun q hq => hg q (List.mem_append.mpr (Or.inr hq))) p' hp''

/-- **Exercise 7.19 — faithfulness of `PFmapComb`.** Under the function-space correspondence of
Theorem 3.10 (`toFilter f` is the point of `(D → E)` fixed by `f`), `PFmapComb` really does send
`f` to `ℙf`, at **every** `f` — not merely the finite/principal points. The forward direction is
immediate; the backward direction is where the work is: given `ℙf ∈ Ψ`, `exists_stepFun_forall_PFmap_rel`
manufactures a finite neighbourhood `stepFun M ∋ f` all of whose members `g` already satisfy `ℙg ∈ Ψ`,
i.e. `Ψ` is reached from a genuine (finite) neighbourhood of `f`, exactly as continuity demands. -/
theorem PFmapComb_toElementMap (f : ApproximableMap V W) :
    (PFmapComb V W).toElementMap (toFilter f) = toFilter (PFmap f) := by
  apply Element.ext
  intro Ψ
  simp only [mem_toElementMap, mem_toFilter, PFmapComb_rel]
  constructor
  · rintro ⟨Φ, ⟨_, hΦf⟩, _, hΨmem, hbody⟩
    exact ⟨hΨmem, hbody f hΦf⟩
  · rintro ⟨hΨmem, hfΨ⟩
    obtain ⟨⟨L₂, hL₂, rfl⟩, -⟩ := hΨmem
    obtain ⟨M, hMmem, hMrel, hMgen⟩ :=
      exists_stepFun_forall_PFmap_rel f L₂ hL₂ (mem_stepFun.mp hfΨ)
    have hΦmem : (funSpace V W).mem (stepFun M) := ⟨⟨M, hMmem, rfl⟩, f, mem_stepFun.mpr hMrel⟩
    have hΨmem' : (funSpace V.PowerDomain W.PowerDomain).mem (stepFun L₂) :=
      ⟨⟨L₂, hL₂, rfl⟩, PFmap f, hfΨ⟩
    exact ⟨stepFun M, ⟨hΦmem, mem_stepFun.mpr hMrel⟩, hΦmem, hΨmem',
      fun g hg => mem_stepFun.mpr (hMgen g (mem_stepFun.mp hg))⟩

end

section
set_option linter.unusedVariables false

theorem example_719.{u_1, u_2, u_3} : And
  (And
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))))
          (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.PFmap α α V V
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))))
        (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
          (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) (consV : Nat → Nat)
          (hconsVp : Nat.Primrec consV)
          (hconsVs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                    (@Inter.inter (Set α) (@Set.instInter α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b))))
          (consW : Nat → Nat) (hconsWp : Nat.Primrec consW)
          (hconsWs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consW (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q k)
                    (@Inter.inter (Set β) (@Set.instInter β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b))))
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
          @DomainTheory.NeighbourhoodSystems.ComputableMap α β V W P Q f →
            @DomainTheory.NeighbourhoodSystems.ComputableMap (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation β W Q consW hconsWp hconsWs)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
      (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
        (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
        {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
        @DomainTheory.NeighbourhoodSystems.ComputableMap α β V W P Q f →
          Domain.Recursive.REPred₂ fun (c d : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d)))
    (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) {c d : Nat},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
          (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d))
        (∀ (a : Nat),
          @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList c) a →
            ∃ (b : Nat),
              And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList d) b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V W f
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b)))))
  (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) {L₁ : List (Set α)} {L₂ : List (Set β)},
    (∀ (X : Set α),
        @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) L₁ X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X) →
      (∀ (Y : Set β),
          @Membership.mem (Set β) (List (Set β)) (@List.instMembership (Set β)) L₂ Y →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β W Y) →
        Iff
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
            (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
            (⋃ (X : Set α),
              ⋃ (_ : @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) L₁ X),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
            (⋃ (Y : Set β),
              ⋃ (_ : @Membership.mem (Set β) (List (Set β)) (@List.instMembership (Set β)) L₂ Y),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet β W Y))
          (∀ (X : Set α),
            @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) L₁ X →
              ∃ (Y : Set β),
                And (@Membership.mem (Set β) (List (Set β)) (@List.instMembership (Set β)) L₂ Y)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V W f X Y))) :=
  @And.intro
  (And
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))))
          (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.PFmap α α V V
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))))
        (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
          (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) (consV : Nat → Nat)
          (hconsVp : Nat.Primrec consV)
          (hconsVs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                    (@Inter.inter (Set α) (@Set.instInter α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b))))
          (consW : Nat → Nat) (hconsWp : Nat.Primrec consW)
          (hconsWs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consW (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q k)
                    (@Inter.inter (Set β) (@Set.instInter β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b))))
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
          @DomainTheory.NeighbourhoodSystems.ComputableMap α β V W P Q f →
            @DomainTheory.NeighbourhoodSystems.ComputableMap (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation β W Q consW hconsWp hconsWs)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
      (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
        (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
        {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
        @DomainTheory.NeighbourhoodSystems.ComputableMap α β V W P Q f →
          Domain.Recursive.REPred₂ fun (c d : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d)))
    (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) {c d : Nat},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
          (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d))
        (∀ (a : Nat),
          @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList c) a →
            ∃ (b : Nat),
              And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList d) b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V W f
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b)))))
  (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
    {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
    (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) {L₁ : List (Set α)} {L₂ : List (Set β)},
    (∀ (X : Set α),
        @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) L₁ X →
          @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem α V X) →
      (∀ (Y : Set β),
          @Membership.mem (Set β) (List (Set β)) (@List.instMembership (Set β)) L₂ Y →
            @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.mem β W Y) →
        Iff
          (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
            (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
            (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
            (⋃ (X : Set α),
              ⋃ (_ : @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) L₁ X),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet α V X)
            (⋃ (Y : Set β),
              ⋃ (_ : @Membership.mem (Set β) (List (Set β)) (@List.instMembership (Set β)) L₂ Y),
                @DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.upSet β W Y))
          (∀ (X : Set α),
            @Membership.mem (Set α) (List (Set α)) (@List.instMembership (Set α)) L₁ X →
              ∃ (Y : Set β),
                And (@Membership.mem (Set β) (List (Set β)) (@List.instMembership (Set β)) L₂ Y)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V W f X Y)))
  (@And.intro
    (And
      (And
        (And
          (And
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))))
          (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.PFmap α α V V
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))))
        (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
          (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) (consV : Nat → Nat)
          (hconsVp : Nat.Primrec consV)
          (hconsVs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                    (@Inter.inter (Set α) (@Set.instInter α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b))))
          (consW : Nat → Nat) (hconsWp : Nat.Primrec consW)
          (hconsWs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consW (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q k)
                    (@Inter.inter (Set β) (@Set.instInter β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b))))
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
          @DomainTheory.NeighbourhoodSystems.ComputableMap α β V W P Q f →
            @DomainTheory.NeighbourhoodSystems.ComputableMap (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation β W Q consW hconsWp hconsWs)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
      (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
        (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
        {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
        @DomainTheory.NeighbourhoodSystems.ComputableMap α β V W P Q f →
          Domain.Recursive.REPred₂ fun (c d : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d)))
    (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
      {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
      (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
      (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
      (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W) {c d : Nat},
      Iff
        (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
          (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
          (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d))
        (∀ (a : Nat),
          @Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList c) a →
            ∃ (b : Nat),
              And (@Membership.mem Nat (List Nat) (@List.instMembership Nat) (Domain.Recursive.decodeList d) b)
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.rel α β V W f
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                  (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b))))
    (@And.intro
      (And
        (And
          (And
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))))
          (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.PFmap α α V V
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))))
        (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
          (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) (consV : Nat → Nat)
          (hconsVp : Nat.Primrec consV)
          (hconsVs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                    (@Inter.inter (Set α) (@Set.instInter α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b))))
          (consW : Nat → Nat) (hconsWp : Nat.Primrec consW)
          (hconsWs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consW (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q k)
                    (@Inter.inter (Set β) (@Set.instInter β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b))))
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
          @DomainTheory.NeighbourhoodSystems.ComputableMap α β V W P Q f →
            @DomainTheory.NeighbourhoodSystems.ComputableMap (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation β W Q consW hconsWp hconsWs)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
      (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
        {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
        (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
        (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W)
        {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
        @DomainTheory.NeighbourhoodSystems.ComputableMap α β V W P Q f →
          Domain.Recursive.REPred₂ fun (c d : Nat) =>
            @DomainTheory.NeighbourhoodSystems.ApproximableMap.rel (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd α V P c)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Ypd β W Q d))
      (@And.intro
        (And
          (And
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))))
          (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.PFmap α α V V
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))))
        (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
          {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
          (P : @DomainTheory.NeighbourhoodSystems.ComputablePresentation α V)
          (Q : @DomainTheory.NeighbourhoodSystems.ComputablePresentation β W) (consV : Nat → Nat)
          (hconsVp : Nat.Primrec consV)
          (hconsVs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consV (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set α) (@Set.instLE α) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P k)
                    (@Inter.inter (Set α) (@Set.instInter α)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X α V P b))))
          (consW : Nat → Nat) (hconsWp : Nat.Primrec consW)
          (hconsWs :
            ∀ (a b : Nat),
              Iff (@Eq Nat (consW (Nat.pair a b)) (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1))))
                (∃ (k : Nat),
                  @LE.le (Set β) (@Set.instLE β) (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q k)
                    (@Inter.inter (Set β) (@Set.instInter β)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q a)
                      (@DomainTheory.NeighbourhoodSystems.ComputablePresentation.X β W Q b))))
          {f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W},
          @DomainTheory.NeighbourhoodSystems.ComputableMap α β V W P Q f →
            @DomainTheory.NeighbourhoodSystems.ComputableMap (Set α) (Set β)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation α V P consV hconsVp hconsVs)
              (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PDPresentation β W Q consW hconsWp hconsWs)
              (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))
        (@And.intro
          (And
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f))))
          (∀ {α : Type u_1} (V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α),
            @Eq
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V))
              (@DomainTheory.NeighbourhoodSystems.PFmap α α V V
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap α V))
              (@DomainTheory.NeighbourhoodSystems.ApproximableMap.idMap (Set α)
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)))
          (@And.intro
            (∀ {α : Type u_1} {β : Type u_2} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.Element
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.toElementMap
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W)
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.funSpace α β V W)
                  (@DomainTheory.NeighbourhoodSystems.funSpace (Set α) (Set β)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                    (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W))
                  (@DomainTheory.NeighbourhoodSystems.PFmapComb α β V W)
                  (@DomainTheory.NeighbourhoodSystems.toFilter α β V W f))
                (@DomainTheory.NeighbourhoodSystems.toFilter (Set α) (Set β)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            (∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {V : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem α}
              {W : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem β}
              {U : DomainTheory.NeighbourhoodSystems.NeighborhoodSystem γ}
              (g : @DomainTheory.NeighbourhoodSystems.ApproximableMap β γ W U)
              (f : @DomainTheory.NeighbourhoodSystems.ApproximableMap α β V W),
              @Eq
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap (Set α) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U))
                (@DomainTheory.NeighbourhoodSystems.PFmap α γ V U
                  (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp α β γ V W U g f))
                (@DomainTheory.NeighbourhoodSystems.ApproximableMap.comp (Set α) (Set β) (Set γ)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain α V)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain β W)
                  (@DomainTheory.NeighbourhoodSystems.NeighborhoodSystem.PowerDomain γ U)
                  (@DomainTheory.NeighbourhoodSystems.PFmap β γ W U g)
                  (@DomainTheory.NeighbourhoodSystems.PFmap α β V W f)))
            @DomainTheory.NeighbourhoodSystems.PFmapComb_toElementMap @DomainTheory.NeighbourhoodSystems.PFmap_comp)
          @DomainTheory.NeighbourhoodSystems.PFmap_idMap)
        @DomainTheory.NeighbourhoodSystems.PFmap_isComputable)
      @DomainTheory.NeighbourhoodSystems.PFmap_isComputable_Ypd)
    @DomainTheory.NeighbourhoodSystems.PFmap_rel_Ypd_iff)
  @DomainTheory.NeighbourhoodSystems.PFmap_rel_fin
end

end DomainTheory.NeighbourhoodSystems
end
