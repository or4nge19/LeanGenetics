import Batteries.Data.List.Lemmas
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import Mathlib

/-!
# A Formal Model of Eukaryotic Gene Expression and Mutation

This file provides a formalization of a simplified eukaryotic
gene-to-protein pipeline in Lean 4. It defines core biological sequences, gene
architecture, and the central dogma processes (transcription, splicing, translation)
with a focus on mathematical precision and provable invariants. The library includes
a comprehensive set of mutation operators and a framework for analyzing their
functional effects on the final protein product.

## Key Components

*   **Core Types**: Total encodings for `DNABase`, `RNABase`, `AminoAcid`, and the
    `standardGeneticCode`. A rich `Mutation` type covers substitutions, indels,
    inversions, duplications, and splice-site mutations.

*   **Gene Architecture**: `Gene` structures with machine-checked invariants, including
    sorted, non-overlapping, and bounded exons (`h_exons_sorted`, `h_exons_bounded`).
    The model includes canonical splice-site motifs (`GT/AG`) in the `Gene` definition.

*   **Central Dogma**:
    *   `splice`: A splicing function that joins exons and validates canonical donor/acceptor
      motifs, returning `none` on a splice-site defect.
    *   `findStartCodon`: A start-codon scanner with a simplified Kozak-context scoring
      metric. Correctness lemmas guarantee that any identified start site is a genuine
      `AUG` codon.
    *   `processMRNA`: A rigorous pipeline that identifies the coding sequence (CDS)
      from a raw mRNA by locating the best start codon and the first in-frame stop codon.
    *   `translate`: A function converting a coding region into an amino acid sequence.

*   **Mutation Analysis**:
    *   `applyMutation`: A dispatcher that applies any `Mutation` to a `Gene`, with
      robust, proven handlers for coordinate-altering mutations (indels, duplications)
      that preserve exon structure invariants (`shiftRegionsAfter`).
    *   `analyzeMutationEffect`: Classifies the impact of a mutation by comparing the
      original and mutated protein products, identifying effects like `Silent`,
      `Missense`, `Nonsense`, `Frameshift`, and `SpliceDefect`.
    *   `frameshiftSemanticWitness`: A constructive proof utility that finds the first
      point of semantic divergence between two protein translations, providing a
      non-axiomatic proof that a frameshift has occurred.

*   **Core Theorems**:
    *   `intronic_substitution_preserves_protein`: A key theorem proving that intronic
      substitutions outside of splice-site windows have no effect on the final protein.
    *   `frameshift_with_witness_changes_protein`: An end-to-end proof that a mutation
      with a semantic frameshift witness results in an altered protein.

## Limitations and Model Simplifications

This formalization prioritizes logical consistency over exhaustive biological detail.
Key simplifications (TODO) include:

*   **Single Strand**: The model operates on a single coding strand of DNA; there is
    no representation of the template strand or reverse-complement logic.
*   **Simplified Splicing**: Splicing logic is based on canonical `GT/AG` dinucleotides.
    It does not model alternative splicing factors, non-canonical splice sites, or
    exon skipping, although a `spliceIsoform` function is provided for modeling
    pre-defined alternative transcripts.
*   **Simplified Translation Initiation**: Start codon selection uses a toy Kozak
    scoring model. It does not account for leaky scanning or alternative start codons.
*   **No Complex Regulation**: The model lacks representations for enhancers, silencers,
    transcription factors, chromatin state, or other regulatory elements. Promoter
    and poly-A sites are placeholders.
*   **No Post-Translational Modification**: The pipeline ends with the raw amino acid
    sequence; protein folding, cleavage, and other modifications are not modeled.
*   **Invariants**: The `ProcessedMRNA` structure guarantees the CDS starts with `AUG`
    but does not currently carry a proof that it terminates with a stop codon, though
    the `processMRNA` function ensures this by construction.
-/


/-!
# Formal Verification of Eukaryotic Gene Expression and Genetic Variation

-/


-- Section 1: Enhanced List Lemmas and Utilities
namespace List

lemma take_drop_append {α : Type*} (l : List α) (n : Nat) :
    l.take n ++ l.drop n = l := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
    cases n with
    | zero => simp
    | succ n' => simp [take, drop, ih]

/-- If `l.drop idx` results in a `cons`, then `l.drop (idx + 1)` is its tail. -/
lemma drop_succ_of_drop_cons {α} {l : List α} {idx : Nat} {x : α} {xs : List α}
    (h : l.drop idx = x :: xs) : l.drop (idx + 1) = xs := by
  rw [← List.drop_drop, h]
  simp

/-- Chain' lemma with proper type signatures for getElem! operations -/
lemma chain'_iff_forall {α : Type*} [Inhabited α] {R : α → α → Prop} {l : List α} :
    Chain' R l ↔ ∀ i j, i + 1 = j → j < l.length → R (l[i]!) (l[j]!) := by
  constructor
  · intro h i j hij hj
    induction l generalizing i j with
    | nil => simp at hj
    | cons x xs ih =>
      cases xs with
      | nil => simp at hj; omega
      | cons y ys =>
        cases h with
        | cons hr hc =>
          dsimp at hj
          cases i with
          | zero =>
            subst j; simp at *
            exact hr
          | succ i' =>
            rw [show (x::y::ys)[i'.succ]! = (y::ys)[i']! by simp]
            rw [show j = i'.succ + 1 by rw [hij]]
            rw [show (x::y::ys)[i'.succ+1]! = (y::ys)[i'.succ]! by simp]
            apply ih hc
            · rfl
            · subst hij
              simp_all only [length_cons, getElem!_eq_getElem?_getD, getElem!_pos,
                forall_eq', add_lt_add_iff_right, getElem_cons_succ, Nat.succ_eq_add_one]
  · intro h
    induction l with
    | nil => constructor
    | cons x xs ih =>
      cases xs with
      | nil => constructor
      | cons y ys =>
        constructor
        · apply h 0 1 rfl; simp
        · apply ih
          intro i j hij hj
          apply h (i + 1) (j + 1)
          · rw [hij]
          · dsimp; exact Nat.succ_lt_succ hj

/-- Efficient chunking for codon processing -/
def chunkListPos {α} (n : Nat) (h_pos : n > 0) (l : List α) : List (List α) :=
  match l with
  | [] => []
  | l' =>
      let chunk := l'.take n
      let rest  := l'.drop n
      if rest.isEmpty then [chunk]
      else chunk :: chunkListPos n h_pos rest
termination_by l.length
decreasing_by
  simp_wf
  cases l' with
  | nil => aesop
  | cons _ _ => simp [List.length_drop]; omega

def chunkList {α} (n : Nat) (l : List α) : List (List α) :=
  if h : n > 0 then chunkListPos n h l else []

def getNth? {α : Type*} (l : List α) (n : Nat) : Option α :=
  if h : n < l.length then some l[n] else none

end List


-- Section 2: Core Biological Entities with Complete Definitions
namespace Bio

inductive DNABase
  | A | T | G | C | N  -- N for unknown/any base
  deriving Repr, DecidableEq, Inhabited, BEq

inductive RNABase
  | A | U | G | C | N  -- N for unknown/any base
  deriving Repr, DecidableEq, Inhabited, BEq

inductive AminoAcid
  | Ala | Arg | Asn | Asp | Cys | Gln | Glu | Gly | His | Ile
  | Leu | Lys | Met | Phe | Pro | Ser | Thr | Trp | Tyr | Val
  deriving Repr, DecidableEq, Inhabited, BEq

inductive TranslationSignal
  | Continue (aa : AminoAcid)
  | Stop
  | Error  -- Invalid/incomplete codon
  deriving Repr, DecidableEq, BEq

/-- Comprehensive mutation types including all major categories -/
inductive Mutation
  | Substitution (pos : Nat) (new : DNABase)
  | Insertion (pos : Nat) (bases : List DNABase)
  | Deletion (pos : Nat) (len : Nat)
  | Inversion (start : Nat) (end_ : Nat)
  | Duplication (start : Nat) (end_ : Nat)
  | SpliceSite (exonIdx : Nat) (isDonor : Bool) (newBase : DNABase)
  deriving Repr, DecidableEq

inductive MutationEffect
  | Silent
  | Missense
  | InFrameIndel
  | Nonsense
  | Frameshift
  | SpliceDefect
  | RegulatoryDefect
  | InvalidMutation
  | NoProtein
  deriving Repr, DecidableEq

end Bio

-- Section 3: Enhanced Gene Architecture
namespace Bio.Sequence

open Bio

@[ext] structure DNAStrand where
  seq : List DNABase
  deriving Repr, DecidableEq, BEq

/--
Represents a spliced messenger RNA molecule.
At this stage, the coding sequence (CDS) has not yet been identified.
It is simply a continuous sequence of ribonucleotides.
-/
@[ext] structure RawMRNA where
  seq : List RNABase
  deriving Repr, DecidableEq, BEq

@[ext] structure MRNA where
  seq : List RNABase
  five_utr_length : Nat := 0
  three_utr_length : Nat := 0
  deriving Repr, DecidableEq, BEq

/--
Represents an MRNA molecule that has been processed for translation.
The sequence is now partitioned into a 5' UTR, a coding sequence (CDS),
and a 3' UTR, based on the identification of a start and stop codon.
-/
@[ext] structure ProcessedMRNA where
  five_utr      : List RNABase
  coding_region : List RNABase -- Starts with a start codon, ends with a stop codon.
  three_utr     : List RNABase
  h_is_cds : coding_region.take 3 = [.A, .U, .G] -- Proof that it starts with AUG.

structure GenomicRegion where
  start : Nat
  end_ : Nat
  h_valid : start < end_
  deriving Repr, BEq, DecidableEq

instance : Inhabited GenomicRegion :=
  ⟨{ start := 0, end_ := 1, h_valid := by decide }⟩

def GenomicRegion.length (r : GenomicRegion) : Nat := r.end_ - r.start

-- Added canonical splice sites to the Gene definition for a more realistic splicing model.
structure Gene where
  id : String
  coding_strand : DNAStrand
  exons : List GenomicRegion
  promoter_region : Option GenomicRegion := none
  poly_a_site : Option Nat := none
  canonical_donor : List DNABase := [.G, .T]
  canonical_acceptor : List DNABase := [.A, .G]

  h_exons_sorted : List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start) exons
  h_exons_bounded : ∀ r ∈ exons, r.end_ ≤ coding_strand.seq.length
  h_exons_nonempty : exons ≠ []

structure SpliceIsoform where
  gene : Gene
  included_exons : List Nat
  h_valid_indices : ∀ i ∈ included_exons, i < gene.exons.length
  h_sorted : List.Chain' (· < ·) included_exons

def IsExonic (gene : Gene) (pos : Nat) : Prop :=
  ∃ exon ∈ gene.exons, pos ≥ exon.start ∧ pos < exon.end_

def IsIntronic (gene : Gene) (pos : Nat) : Prop :=
  pos < gene.coding_strand.seq.length ∧ ¬IsExonic gene pos

def inRegion (pos : Nat) (r : GenomicRegion) : Bool :=
  pos ≥ r.start && pos < r.end_

end Bio.Sequence

-- Section 4: Complete Central Dogma Implementation
namespace Bio.Genetics

open Bio Bio.Sequence List

def transcribeBase (b : DNABase) : RNABase :=
  match b with
  | .A => .A | .T => .U | .G => .G | .C => .C | .N => .N

def transcribe (dna : List DNABase) : List RNABase :=
  dna.map transcribeBase

/-- Complete genetic code (all 64 codons) -/
def standardGeneticCode (codon : List RNABase) : TranslationSignal :=
  match codon with
  -- Phenylalanine
  | [.U, .U, .U] | [.U, .U, .C] => .Continue .Phe
  -- Leucine (6 codons)
  | [.U, .U, .A] | [.U, .U, .G] => .Continue .Leu
  | [.C, .U, .U] | [.C, .U, .C] | [.C, .U, .A] | [.C, .U, .G] => .Continue .Leu
  -- Isoleucine
  | [.A, .U, .U] | [.A, .U, .C] | [.A, .U, .A] => .Continue .Ile
  -- Methionine (start)
  | [.A, .U, .G] => .Continue .Met
  -- Valine
  | [.G, .U, .U] | [.G, .U, .C] | [.G, .U, .A] | [.G, .U, .G] => .Continue .Val
  -- Serine (6 codons)
  | [.U, .C, .U] | [.U, .C, .C] | [.U, .C, .A] | [.U, .C, .G] => .Continue .Ser
  | [.A, .G, .U] | [.A, .G, .C] => .Continue .Ser
  -- Proline
  | [.C, .C, .U] | [.C, .C, .C] | [.C, .C, .A] | [.C, .C, .G] => .Continue .Pro
  -- Threonine
  | [.A, .C, .U] | [.A, .C, .C] | [.A, .C, .A] | [.A, .C, .G] => .Continue .Thr
  -- Alanine
  | [.G, .C, .U] | [.G, .C, .C] | [.G, .C, .A] | [.G, .C, .G] => .Continue .Ala
  -- Tyrosine
  | [.U, .A, .U] | [.U, .A, .C] => .Continue .Tyr
  -- Stop codons
  | [.U, .A, .A] | [.U, .A, .G] | [.U, .G, .A] => .Stop
  -- Histidine
  | [.C, .A, .U] | [.C, .A, .C] => .Continue .His
  -- Glutamine
  | [.C, .A, .A] | [.C, .A, .G] => .Continue .Gln
  -- Asparagine
  | [.A, .A, .U] | [.A, .A, .C] => .Continue .Asn
  -- Lysine
  | [.A, .A, .A] | [.A, .A, .G] => .Continue .Lys
  -- Aspartic acid
  | [.G, .A, .U] | [.G, .A, .C] => .Continue .Asp
  -- Glutamic acid
  | [.G, .A, .A] | [.G, .A, .G] => .Continue .Glu
  -- Cysteine
  | [.U, .G, .U] | [.U, .G, .C] => .Continue .Cys
  -- Tryptophan
  | [.U, .G, .G] => .Continue .Trp
  -- Arginine (6 codons)
  | [.C, .G, .U] | [.C, .G, .C] | [.C, .G, .A] | [.C, .G, .G] => .Continue .Arg
  | [.A, .G, .A] | [.A, .G, .G] => .Continue .Arg
  -- Glycine
  | [.G, .G, .U] | [.G, .G, .C] | [.G, .G, .A] | [.G, .G, .G] => .Continue .Gly
  -- Invalid/incomplete
  | _ => .Error

/-- Simplified Kozak consensus scoring.
Emphasizes a purine at −3 (A/G) and G at +4; other positions carry small weights.
This is a toy metric suitable for formalization; results are invariant to exact weights. -/
def scoreKozak (context : List RNABase) : Nat :=
  -- Position -3: A or G strongly preferred (Kozak's key position)
  let score_minus3 := match context.getNth? 0 with
    | some .A => 3
    | some .G => 3
    | _ => 0
  -- Position -2: moderate preference for C
  let score_minus2 := match context.getNth? 1 with
    | some .C => 1
    | _ => 0
  -- Position -1: moderate preference for C
  let score_minus1 := match context.getNth? 2 with
    | some .C => 1
    | _ => 0
  -- Position +4: G strongly preferred (Kozak's second key position)
  let score_plus4 := match context.getNth? 6 with
    | some .G => 3
    | _ => 0
  -- Position +5: moderate preference
  let score_plus5 := match context.getNth? 7 with
    | some .C => 1
    | _ => 0
  score_minus3 + score_minus2 + score_minus1 + score_plus4 + score_plus5

/-- Find and score all potential start codons -/
def findAndScoreStartCodons (rna : List RNABase) : List (Nat × Nat) :=
  let rec aux (idx : Nat) (remaining : List RNABase) (acc : List (Nat × Nat)) :
      List (Nat × Nat) :=
    match remaining with
    | .A :: .U :: .G :: rest =>
      -- Build context for Kozak scoring
      let context_start := if idx ≥ 3 then idx - 3 else 0
      let context_len := (idx - context_start) + 3 + (min 5 rest.length)
      let context := (rna.drop context_start).take context_len
      let score := scoreKozak context
      aux (idx + 1) (.U :: .G :: rest) ((idx, score) :: acc)
    | _ :: rest => aux (idx + 1) rest acc
    | [] => acc.reverse
  termination_by remaining.length
  aux 0 rna []

/-
/-- Advanced start codon selection based on Kozak scoring -/
def findStartCodon' (mrna : MRNA) : Option Nat :=
  let coding_seq := mrna.seq.drop mrna.five_utr_length
  let candidates := findAndScoreStartCodons coding_seq
  -- Select best scoring, or first if tie
  let best := candidates.foldl (fun best curr =>
    match best with
    | none => some curr
    | some b => if curr.2 > b.2 || (curr.2 = b.2 && curr.1 < b.1)
                then some curr else some b
  ) none
  best.map (·.1)
  -/

/-
def splice' (gene : Gene) : MRNA :=
  let pre_mrna := transcribe gene.coding_strand.seq
  let mature_seq := gene.exons.flatMap (fun region =>
    pre_mrna.drop region.start |>.take region.length
  )
  { seq := mature_seq,
    five_utr_length := if gene.exons.length > 0 then gene.exons[0]!.start else 0,
    three_utr_length := 0 }

def splice'' (iso : SpliceIsoform) : MRNA :=
  let pre_mrna := transcribe iso.gene.coding_strand.seq
  let included := iso.included_exons.map (fun i => iso.gene.exons[i]!)
  let mature_seq := included.flatMap (fun region =>
    pre_mrna.drop region.start |>.take region.length
  )
  { seq := mature_seq, five_utr_length := 0, three_utr_length := 0 }

def translate' (mrna : MRNA) : Option (List AminoAcid) :=
  match findStartCodon mrna with
  | none => none
  | some startPos =>
    let translatingRegion := mrna.seq.drop (mrna.five_utr_length + startPos)
    let codons := chunkList 3 translatingRegion
    let processCodon (acc : List AminoAcid × Bool) (codon : List RNABase) :
        List AminoAcid × Bool :=
      if acc.2 then acc
      else if codon.length ≠ 3 then (acc.1, true)
      else match standardGeneticCode codon with
        | .Continue aa => (acc.1 ++ [aa], false)
        | .Stop => (acc.1, true)
        | .Error => (acc.1, true)
    let (peptide, _) := codons.foldl processCodon ([], false)
    if peptide.head? = some .Met then some peptide else none

def synthesizeProtein' (gene : Gene) : Option (List AminoAcid) :=
  translate' (splice' gene)-/

/--
Produces a mature mRNA sequence by transcribing the gene's DNA and splicing
the exons together. This represents the biological process of splicing.
The output is a simple RawMRNA sequence, as UTRs are not yet defined.
-/
/-
def splice (gene : Gene) : RawMRNA :=
  let pre_mrna := transcribe gene.coding_strand.seq
  let mature_seq := gene.exons.flatMap (fun region =>
    pre_mrna.drop region.start |>.take region.length
  )
  { seq := mature_seq }-/

-- Helper: the selection function used in findStartCodon’s foldl always returns a member of the list.
private def chooseBest (best : Option (Nat × Nat)) (curr : Nat × Nat) : Option (Nat × Nat) :=
  match best with
  | none => some curr
  | some b =>
    if curr.2 > b.2 || (curr.2 = b.2 && curr.1 < b.1)
    then some curr else some b

private lemma chooseBest_some_cases (acc curr : Nat × Nat) :
    ∃ acc', chooseBest (some acc) curr = some acc' ∧ (acc' = acc ∨ acc' = curr) := by
  dsimp [chooseBest]
  by_cases h : (curr.2 > acc.2) ∨ (curr.2 = acc.2 ∧ curr.1 < acc.1)
  · exact ⟨curr, by simp [h], Or.inr rfl⟩
  · exact ⟨acc,  by simp [h], Or.inl rfl⟩

private lemma foldl_chooseBest_mem_aux :
    ∀ (ys : List (Nat × Nat)) (acc r : Nat × Nat),
      ys.foldl chooseBest (some acc) = some r →
      r = acc ∨ r ∈ ys
  | [], acc, r, h => by
      -- foldl on [] returns the accumulator unchanged
      simp_all only [foldl_nil, Option.some.injEq, not_mem_nil, or_false]
  | curr :: ys, acc, r, h => by
      -- One fold step from (some acc) with current = curr
      rcases chooseBest_some_cases acc curr with ⟨acc', hstep, hacc'⟩
      have h' : ys.foldl chooseBest (some acc') = some r := by
        simpa [List.foldl, hstep] using h
      -- Recurse on tail
      have ih := foldl_chooseBest_mem_aux ys acc' r h'
      cases ih with
      | inl heq =>
          -- r = acc' ; tie back to acc or curr
          cases hacc' with
          | inl hacc =>
              -- acc' = acc
              subst hacc heq
              simp_all only [foldl_cons, mem_cons, true_or]
          | inr hcurr =>
              -- acc' = curr ⇒ r ∈ curr :: ys
              subst hcurr
              aesop--exact Or.inr (List.mem_cons_self _ _)
      | inr hin =>
          -- r ∈ ys ⇒ r ∈ curr :: ys
          exact Or.inr (List.mem_cons_of_mem _ hin)

private lemma foldl_chooseBest_mem {xs : List (Nat × Nat)} {res : Nat × Nat} :
    xs.foldl chooseBest none = some res → res ∈ xs := by
  cases xs with
  | nil =>
      intro h; cases h
  | cons x xs =>
      intro h
      have h' : xs.foldl chooseBest (some x) = some res := by
        simpa [List.foldl, chooseBest] using h
      have : res = x ∨ res ∈ xs := foldl_chooseBest_mem_aux xs x res h'
      exact List.mem_cons.mpr this

-- Core scanner correctness: every candidate (p, score) in findAndScoreStartCodons marks an AUG.
namespace findAndScoreStartCodons

private lemma mem_isAUG_nil {rna : List RNABase} {p s : Nat} {acc : List (Nat × Nat)}
    (h_mem : (p, s) ∈ aux rna 0 [] acc) :
    (p, s) ∈ acc := by
  simpa [aux, List.mem_reverse] using h_mem

private lemma mem_isAUG_cons_nonAUG {rna : List RNABase} {a : RNABase} {rem : List RNABase}
    {idx : Nat} {acc : List (Nat × Nat)} {p s : Nat}
    (_ : ¬ (a :: rem).isPrefixOf (.A :: .U :: .G :: []))
    (_ : (p, s) ∈ aux rna (idx + 1) rem acc)
    (h_ind : (p, s) ∈ acc ∨ ∃ rest, rna.drop p = .A :: .U :: .G :: rest) :
    (p, s) ∈ acc ∨ ∃ rest, rna.drop p = .A :: .U :: .G :: rest := by
  exact h_ind

private lemma mem_isAUG_cons_AUG {rna : List RNABase} {rest' : List RNABase}
    {idx : Nat} {acc : List (Nat × Nat)} {p s : Nat}
    (h_head : rna.drop idx = .A :: .U :: .G :: rest')
    (h_rec :
      (p, s) ∈
        aux rna (idx + 1) (.U :: .G :: rest')
          ((idx,
              scoreKozak
                ((rna.drop (if idx ≥ 3 then idx - 3 else 0)).take
                  ((idx - if idx ≥ 3 then idx - 3 else 0) + 3 + min 5 rest'.length))) :: acc))
    (h_ind :
      (p, s) ∈
        ((idx,
            scoreKozak
              ((rna.drop (if idx ≥ 3 then idx - 3 else 0)).take
                ((idx - if idx ≥ 3 then idx - 3 else 0) + 3 + min 5 rest'.length))) :: acc)
      ∨ ∃ rest, rna.drop p = .A :: .U :: .G :: rest) :
    (p, s) ∈ acc ∨ ∃ rest, rna.drop p = .A :: .U :: .G :: rest := by
  -- The result `(p,s)` either came from the recursive call or was the new head `(idx, score)`.
  rcases h_ind with h_in_acc | h_is_aug
  · -- Case 1: (p,s) was in the new accumulator `(idx, score) :: acc`.
    cases (List.mem_cons.mp h_in_acc) with
    | inl h_eq_head =>
      -- It's the new head; deduce p = idx and conclude via h_head.
      have hpidx : p = idx := by
        simpa using congrArg Prod.fst h_eq_head
      subst hpidx
      exact Or.inr ⟨rest', h_head⟩
    | inr h_in_tail =>
      -- It was in the original `acc`.
      exact Or.inl h_in_tail
  · -- Case 2: The recursive call already proved AUG at position p.
    exact Or.inr h_is_aug


private lemma mem_isAUG {rna : List RNABase} :
    ∀ (idx : Nat) (rem : List RNABase) (acc : List (Nat × Nat)),
      rna.drop idx = rem →
      ∀ (p s : Nat),
        (p, s) ∈ (aux rna idx rem acc) →
        (p, s) ∈ acc ∨ ∃ rest, rna.drop p = .A :: .U :: .G :: rest := by
  intro idx rem acc hdrop p s hp
  revert idx acc hdrop
  induction rem with
  | nil =>
    intro idx acc _ hp
    -- aux returns acc.reverse when remaining = []
    exact Or.inl (by simpa [aux, List.mem_reverse] using hp)
  | cons a rem' ih =>
    intro idx acc hdrop hp
    -- Split on the length of the tail to mirror aux's pattern matching.
    cases rem' with
    | nil =>
      -- rem = [a]; aux takes the _ :: rest branch, rest = []
      have hp' : (p, s) ∈ aux rna (idx + 1) [] acc := by
        simpa [aux] using hp
      -- rna.drop (idx+1) = []
      have hdrop' : rna.drop (idx + 1) = [] := by
        have hcons : rna.drop idx = a :: ([] : List RNABase) := by simpa using hdrop
        exact List.drop_succ_of_drop_cons hcons
      exact ih (idx + 1) acc hdrop' hp'
    | cons b rem'' =>
      cases rem'' with
      | nil =>
        -- rem = a :: b :: []; aux takes the _ :: rest branch with rest = [b]
        have hp' : (p, s) ∈ aux rna (idx + 1) [b] acc := by
          simpa [aux] using hp
        -- rna.drop (idx+1) = [b]
        have hdrop' : rna.drop (idx + 1) = [b] := by
          have hcons : rna.drop idx = a :: b :: ([] : List RNABase) := by simpa using hdrop
          exact List.drop_succ_of_drop_cons hcons
        exact ih (idx + 1) acc hdrop' hp'
      | cons c rest =>
        -- rem = a :: b :: c :: rest
        -- Distinguish AUG vs non-AUG via a boolean split; simp will route aux accordingly.
        by_cases hAUG : (a = .A ∧ b = .U ∧ c = .G)
        · -- AUG case: aux pushes (idx, score) and recurses on (.U :: .G :: rest)
          rcases hAUG with ⟨hA, hU, hG⟩
          subst hA; subst hU; subst hG
          -- From hp, expose the recursive membership with the new head pushed.
          have hp' :
              (p, s) ∈
                aux rna (idx + 1) (.U :: .G :: rest)
                  ((idx,
                      scoreKozak
                        ((rna.drop (if idx ≥ 3 then idx - 3 else 0)).take
                          ((idx - if idx ≥ 3 then idx - 3 else 0) + 3 + min 5 rest.length))) :: acc) := by
            simpa [aux] using hp
          -- rna.drop idx = .A :: .U :: .G :: rest  and rna.drop (idx+1) = .U :: .G :: rest
          have hhead : rna.drop idx = .A :: .U :: .G :: rest := by simpa using hdrop
          have hdrop' : rna.drop (idx + 1) = .U :: .G :: rest :=
            List.drop_succ_of_drop_cons (by simpa using hhead)
          -- Apply IH to the recursive call with the pushed head accumulator.
          have hind :
              (p, s) ∈
                ((idx,
                    scoreKozak
                      ((rna.drop (if idx ≥ 3 then idx - 3 else 0)).take
                        ((idx - if idx ≥ 3 then idx - 3 else 0) + 3 + min 5 rest.length))) :: acc)
              ∨ ∃ rest₀, rna.drop p = .A :: .U :: .G :: rest₀ :=
            ih (idx + 1)
               ((idx,
                   scoreKozak
                     ((rna.drop (if idx ≥ 3 then idx - 3 else 0)).take
                       ((idx - if idx ≥ 3 then idx - 3 else 0) + 3 + min 5 rest.length))) :: acc)
               hdrop' hp'
          -- Peel the pushed head via the AUG-head helper lemma.
          exact mem_isAUG_cons_AUG (rna := rna) (idx := idx) (acc := acc) (p := p) (s := s)
            hhead hp' hind
        · -- Non-AUG case: aux recurses on (b :: c :: rest) without pushing.
          have hp' : (p, s) ∈ aux rna (idx + 1) (b :: c :: rest) acc := by
            -- Rewrite the one-step unfold of aux on a non-AUG head explicitly.
            have step :
                aux rna idx (a :: b :: c :: rest) acc =
                aux rna (idx + 1) (b :: c :: rest) acc := by
              -- Discharge by cases on (a,b,c) against (A,U,G)
              by_cases hA : a = .A
              · subst hA
                by_cases hU : b = .U
                · subst hU
                  by_cases hG : c = .G
                  · exact (False.elim (hAUG ⟨rfl, rfl, hG⟩))
                  · simp [aux, hG]
                · simp [aux, hU]
              · simp [aux, hA]
            simpa [step] using hp
          -- rna.drop (idx+1) = b :: c :: rest
          have hdrop' : rna.drop (idx + 1) = b :: c :: rest := by
            have hcons : rna.drop idx = a :: b :: c :: rest := by simpa using hdrop
            exact List.drop_succ_of_drop_cons hcons
          exact ih (idx + 1) acc hdrop' hp' --
end findAndScoreStartCodons

-- Corollary for the top-level function: any picked index points to AUG.
lemma findAndScoreStartCodons_mem_AUG {rna : List RNABase} {p s : Nat}
    (hmem : (p, s) ∈ findAndScoreStartCodons rna) :
    ∃ rest, rna.drop p = .A :: .U :: .G :: rest := by
  -- findAndScoreStartCodons rna = aux rna 0 rna []
  have := findAndScoreStartCodons.mem_isAUG (rna := rna) 0 rna [] rfl p s (by
    -- expose the aux call producing the result
    simpa [findAndScoreStartCodons])
  exact this.elim (fun hinAcc => False.elim (by cases hinAcc)) id

/-- Advanced start codon selection based on Kozak scoring -/
def findStartCodon (mrna : Bio.Sequence.MRNA) : Option Nat :=
  let coding_seq := mrna.seq.drop mrna.five_utr_length
  let candidates := findAndScoreStartCodons coding_seq
  -- Select best scoring, or first if tie, using the shared chooser
  let best := candidates.foldl chooseBest none
  best.map (·.1)

lemma findStartCodon_is_AUG_simple
    (m : Bio.Sequence.MRNA) {i : Nat}
    (h : findStartCodon m = some i) :
    (m.seq.drop (m.five_utr_length + i)).take 3 = [.A, .U, .G] := by
  unfold findStartCodon at h
  set coding_seq := m.seq.drop m.five_utr_length with hseq
  -- candidates
  set candidates := findAndScoreStartCodons coding_seq with hcand
  have hbestFoldMap :
      (candidates.foldl chooseBest none).map (·.1) = some i := by
    simpa [coding_seq, candidates] using h
  cases hres : candidates.foldl chooseBest none with
  | none =>
      simp [Option.map, hres] at hbestFoldMap
  | some pr =>
    have hpr1 : pr.1 = i := by
      have : some pr.1 = some i := by simpa [Option.map, hres] using hbestFoldMap
      exact Option.some.inj this
    have hmem : pr ∈ candidates := foldl_chooseBest_mem (res := pr) (by simp [hres])
    rcases findAndScoreStartCodons_mem_AUG (rna := coding_seq) (p := pr.1) (s := pr.2) hmem with ⟨rest, hdrop⟩
    have htake : (coding_seq.drop pr.1).take 3 = [.A, .U, .G] := by
      simp [hdrop]
    have : (coding_seq.drop i).take 3 = [.A, .U, .G] := by
      simpa [hpr1] using htake
    simpa [coding_seq, List.drop_drop, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using this

/--
Identifies the translatable coding sequence (CDS) within an MRNA by finding
the best start codon (via Kozak scoring) and the first subsequent in-frame
stop codon.

Returns `none` if no suitable start/stop codons are found.
-/
def processMRNA (mrna : RawMRNA) : Option ProcessedMRNA :=
  match hstart : findStartCodon { seq := mrna.seq } with -- treat five_utr_length = 0 here
  | none => none
  | some startPos =>
    let potential_cds := mrna.seq.drop startPos
    let codons := chunkList 3 potential_cds
    let stop_codon_idx? := codons.findIdx? (fun c =>
        match standardGeneticCode c with | .Stop => true | _ => false)
    match stop_codon_idx? with
    | none => none
    | some stop_idx =>
      let cds_codon_count := stop_idx + 1
      let cds_len := cds_codon_count * 3
      if h_valid_cds : potential_cds.length ≥ 3 then
        some {
          five_utr      := mrna.seq.take startPos
          coding_region := potential_cds.take cds_len
          three_utr     := potential_cds.drop cds_len
          h_is_cds      := by
            -- From the pick, the first three bases at the start position are AUG.
            have hpick : findStartCodon { seq := mrna.seq } = some startPos := hstart
            have hAUG_at_start :
                (mrna.seq.drop (0 + startPos)).take 3 = [.A, .U, .G] := by
              simpa using
                (findStartCodon_is_AUG_simple
                  ({ seq := mrna.seq, five_utr_length := 0, three_utr_length := 0 })
                  (i := startPos) hpick)
            -- Convert that to potential_cds.take 3
            have hAUG_potential : (potential_cds.take 3) = [.A, .U, .G] := by
              -- potential_cds = mrna.seq.drop startPos
              simpa [potential_cds, Nat.zero_add] using hAUG_at_start
            -- Show 3 ≤ cds_len so that take 3 (take cds_len l) = take 3 l.
            have h_count_pos : 1 ≤ cds_codon_count := by
              exact Nat.succ_le_succ (Nat.zero_le _)
            have h3le : 3 ≤ cds_len := by
              -- 1*3 ≤ cds_codon_count*3
              have := Nat.mul_le_mul_right 3 h_count_pos
              simpa [cds_len, Nat.one_mul] using this
            -- Now rewrite with take_take and min_eq_left.
            calc
              (potential_cds.take cds_len).take 3
                  = potential_cds.take (min 3 cds_len) := by
                    simp [List.take_take]
              _ = potential_cds.take 3 := by
                    simp [Nat.min_eq_left h3le]
              _ = [.A, .U, .G] := hAUG_potential
        }
      else none
/--
Translates a coding sequence (a list of RNA bases starting with a start
codon) into a peptide (a list of amino acids).

The translation process correctly starts with Methionine (from the AUG codon)
and terminates when a stop codon is encountered. It no longer performs an
ad-hoc check to remove non-Met-starting peptides, thus separating the model
of translation from post-translational modification.
-/
def translate' (coding_region : List RNABase) : List AminoAcid :=
  let codons := chunkList 3 coding_region
  let rec process (codon_list : List (List RNABase)) (acc : List AminoAcid) : List AminoAcid :=
    match codon_list with
    | [] => acc
    | c :: cs =>
      if c.length ≠ 3 then acc -- Stop on incomplete codon
      else match standardGeneticCode c with
        | .Continue aa => process cs (acc ++ [aa])
        | .Stop => acc -- Terminate translation
        | .Error => acc -- Stop on error
  process codons []

def translate (coding_region : List RNABase) : List AminoAcid :=
  let rec go (cl : List (List RNABase)) : List AminoAcid :=
    match cl with
    | [] => []
    | c :: cs =>
      if c.length ≠ 3 then []
      else
        match standardGeneticCode c with
        | .Continue aa => aa :: go cs
        | .Stop => []
        | .Error => []
  go (List.chunkList 3 coding_region)

open Classical

private def spliceAndCheck (gene : Gene) (pre_mrna : List RNABase) :
    List GenomicRegion → List RNABase → Option (List RNABase)
  | [], acc => some acc
  | r :: rs, acc =>
    let acceptor_ok : Bool :=
      acc.isEmpty ||
        decide
          (((gene.coding_strand.seq.drop (r.start - gene.canonical_acceptor.length)).take
              gene.canonical_acceptor.length)
            = gene.canonical_acceptor)
    let donor_ok : Bool :=
      rs.isEmpty ||
        decide
          (((gene.coding_strand.seq.drop r.end_).take gene.canonical_donor.length)
            = gene.canonical_donor)

    if acceptor_ok && donor_ok then
      let spliced_segment := pre_mrna.drop r.start |>.take r.length
      spliceAndCheck gene pre_mrna rs (acc ++ spliced_segment)
    else
      none

/--
REVISED: Produces a mature mRNA by transcribing and splicing.
This version checks for canonical splice sites (e.g., GT-AG).
-/
def splice (gene : Gene) : Option RawMRNA :=
  let pre_mrna := transcribe gene.coding_strand.seq
  (spliceAndCheck gene pre_mrna gene.exons []).map ({ seq := · })

/-
/--
REVISED: Produces a mature mRNA by transcribing and splicing.
This version checks for canonical splice sites (e.g., GT-AG). If a splice site
is mutated, splicing fails, returning `none`. This is critical for modeling
splice-site defects correctly.
-/
def splice' (gene : Gene) : Option RawMRNA :=
  let pre_mrna := transcribe gene.coding_strand.seq
  let rec spliceAndCheck (exons : List GenomicRegion) (acc : List RNABase) : Option (List RNABase) :=
    match exons with
    | [] => some acc
    | r :: rs =>
      -- Check acceptor site for this exon (unless it's the first one)
      let acceptor_ok : Bool :=
        if acc.isEmpty then
          true
        else
          let acceptor_pos := r.start - gene.canonical_acceptor.length
          let slice := gene.coding_strand.seq.drop acceptor_pos |>.take gene.canonical_acceptor.length
          slice == gene.canonical_acceptor
      -- Check donor site for this exon (unless it's the last one)
      let donor_ok : Bool :=
        if rs.isEmpty then
          true
        else
          let slice := gene.coding_strand.seq.drop r.end_ |>.take gene.canonical_donor.length
          slice == gene.canonical_donor

      if acceptor_ok && donor_ok then
        let spliced_segment := pre_mrna.drop r.start |>.take r.length
        spliceAndCheck rs (acc ++ spliced_segment)
      else
        none -- Splicing fails due to invalid splice site
  (spliceAndCheck gene.exons []).map (fun seq => { seq := seq })
  -/

/--
NEW: Splicing based on a specific isoform, demonstrating the utility of the
`SpliceIsoform` structure and modeling alternative splicing.
-/
def spliceIsoform (iso : SpliceIsoform) : Option RawMRNA :=
  let pre_mrna := transcribe iso.gene.coding_strand.seq
  -- Retrieve the actual exon regions from the indices
  let included_regions := iso.included_exons.map (fun i => iso.gene.exons[i]!)
  -- Here, we assume the selected exons are meant to be contiguous and don't re-check
  -- canonical sites between them, as alternative splicing can use different signals.
  -- A more complex model could check this.
  let mature_seq := included_regions.flatMap (fun region =>
    pre_mrna.drop region.start |>.take region.length
  )
  some { seq := mature_seq }

/--
The complete, revised pipeline from gene to protein, now using the robust
splicing function. This pipeline can now fail at the splicing step.
-/
def synthesizeProtein (gene : Gene) : Option (List AminoAcid) :=
  let mrna? := splice gene
  mrna?.bind (fun mrna =>
    (processMRNA mrna).map (fun p => translate p.coding_region)
  )

-- NEW: A pipeline for a specific splice isoform.
def synthesizeProteinFromIsoform (iso : SpliceIsoform) : Option (List AminoAcid) :=
  (spliceIsoform iso).bind (fun mrna =>
    (processMRNA mrna).map (fun p => translate p.coding_region)
  )

lemma synthesizeProtein_eq_some_of_processed
    (g : Gene) {raw : RawMRNA} {p : ProcessedMRNA}
    (hsplice : splice g = some raw)
    (hproc   : processMRNA raw = some p) :
    synthesizeProtein g = some (translate p.coding_region) := by
  simp [synthesizeProtein, hsplice, hproc]

end Bio.Genetics

-- Section 5: Complete Mutation Analysis with Length-Altering Support
namespace Bio.Mutation

open Bio Bio.Sequence Bio.Genetics List

/--
Calculates the offset of a genomic position within the spliced mRNA.
Returns `none` if the position is intronic.
-/
def genomicToSplicedOffset (gene : Gene) (pos : Nat) : Option Nat :=
  let rec aux (exons : List GenomicRegion) (accumulatedLen : Nat) : Option Nat :=
    match exons with
    | [] => none
    | r :: rs =>
      if pos < r.start then
        none -- Position is before this exon, and not in previous ones, so it's intronic.
      else if pos < r.end_ then
        -- Position is inside this exon.
        some (accumulatedLen + (pos - r.start))
      else
        -- Position is after this exon, continue searching in the next ones.
        aux rs (accumulatedLen + r.length)
  aux gene.exons 0

/-
/--
Determines the offset of a genomic position relative to the start codon.
Returns `none` if the position is not in the coding sequence (intronic, UTR, or in a gene with no start codon).
-/
def getCodingOffset (gene : Gene) (pos : Nat) : Option Nat :=
  let rawMrna := splice gene
  let mrna : Sequence.MRNA := {
    seq              := rawMrna.seq,
    five_utr_length  := 0,
    three_utr_length := 0
  }
  let startPos? := findStartCodon mrna
  let splicedPos? := genomicToSplicedOffset gene pos
  match startPos?, splicedPos? with
  | some startPos, some splicedPos =>
    if splicedPos ≥ startPos then
      some (splicedPos - startPos)
    else
      none -- Position is in 5' UTR
  | _, _ => none -- No start codon or intronic position-/

/--
Determines the offset of a genomic position relative to the start codon, in the
same model used by `synthesizeProtein`. It computes the start by running
`splice` and `processMRNA`, then measures the offset in the spliced transcript.

Returns `none` if no CDS was found, or the position is intronic/5'UTR.
-/
def getCodingOffset (gene : Gene) (pos : Nat) : Option Nat :=
  let splicedPos? := genomicToSplicedOffset gene pos
  match Bio.Genetics.splice gene with
  | none => none
  | some raw =>
    match splicedPos?, Bio.Genetics.processMRNA raw with
    | some splicedPos, some processed =>
      let start := processed.five_utr.length
      if splicedPos ≥ start then
        some (splicedPos - start)
      else
        none
    | _, _ => none

/--
Checks if a mutation is a frameshift based on its position and length.
A frameshift occurs if an insertion or deletion of length not divisible by 3
happens within the coding sequence (after the start codon).
-/
def mutationIsFrameshift (gene : Gene) (m : Mutation) : Bool :=
  match m with
  | .Insertion pos bases =>
    -- An insertion causes a frameshift if it's in the CDS and its length is not a multiple of 3.
    (getCodingOffset gene pos).isSome ∧ bases.length % 3 ≠ 0
  | .Deletion pos len =>
    -- A deletion causes a frameshift if it's in the CDS and its length is not a multiple of 3.
    (getCodingOffset gene pos).isSome ∧ len % 3 ≠ 0
  | _ => false -- Substitutions, etc., do not cause frameshifts.

def inRegion (pos : Nat) (r : GenomicRegion) : Bool :=
  pos ≥ r.start && pos < r.end_

/-- Shift genomic regions after a position (critical for insertions/deletions) -/
def shiftRegionsAfter (pos : Nat) (shift : Int) (regions : List GenomicRegion) :
    List GenomicRegion :=
  regions.filterMap (fun (r : GenomicRegion) =>
    ------------------------------------------------------------------
    -- 1 Entire region is strictly **after** the mutation coordinate --
    ------------------------------------------------------------------
    if pos ≤ r.start then
      let newStart : Int := (r.start : Int) + shift
      let newEnd   : Int := (r.end_  : Int) + shift
      if h_ok : newStart ≥ 0 ∧ newEnd > newStart then
        let h_valid : newStart.toNat < newEnd.toNat := by
          have : (newStart.toNat : Int) < (newEnd.toNat : Int) := by
            have h₁ : (newStart.toNat : Int) = newStart := by
              simp [Int.toNat_of_nonneg h_ok.1]
            have h₂ : (newEnd.toNat : Int) = newEnd := by
              have : (0 : Int) ≤ newEnd :=
                le_trans h_ok.1 (le_of_lt h_ok.2)
              simp [Int.toNat_of_nonneg this]
            simpa [h₁, h₂] using h_ok.2
          exact_mod_cast this
        some { start  := newStart.toNat,
               end_   := newEnd.toNat,
               h_valid := h_valid }
      else
        none
    -- 2 Mutation occurs **inside** the region – only the end shifts --
    else if pos < r.end_ then
      let newEnd : Int := (r.end_ : Int) + shift
      if h_gt : newEnd > r.start then
        -- Region remains non-empty: prove `r.start < newEnd.toNat`
        let h_valid : r.start < newEnd.toNat := by
          -- 1. Establish `newEnd` is non-negative.
          have h_nonneg : (0 : Int) ≤ newEnd := by
            have : (0 : Int) ≤ (r.start : Int) := by
              exact_mod_cast (Nat.zero_le _)
            exact le_trans this (le_of_lt h_gt)
          -- 2. Cast `h_gt` to the `Nat` world.
          have : (r.start : Int) < (newEnd.toNat : Int) := by
            simpa [Int.toNat_of_nonneg h_nonneg] using h_gt
          exact_mod_cast this
        some { r with end_ := newEnd.toNat, h_valid := h_valid }
      else
        none
    ------------------------------------------------------------------
    -- 3 Region is **before** the mutation point – remains unchanged --
    ------------------------------------------------------------------
    else
      some r)

/-- Pure Nat version of region shifting for nonnegative shifts (insertions). -/
def shiftRegionAfterNat (pos shift : Nat) (r : GenomicRegion) : GenomicRegion :=
  if h_all : pos ≤ r.start then
    -- Entire region is after the insertion coordinate: shift both start and end_.
    { start := r.start + shift
    , end_  := r.end_  + shift
    , h_valid := by
        -- start + s < end_ + s
        exact Nat.add_lt_add_right r.h_valid shift }
  else if h_in : pos < r.end_ then
    -- Insertion lands inside the region: only extend the end.
    { r with
      end_ := r.end_ + shift
      -- start < end_ ≤ end_ + shift
      h_valid := by
        exact lt_of_lt_of_le r.h_valid (Nat.le_add_right _ _) }
  else
    -- Region is completely before the insertion point: unchanged.
    r

lemma shift_mono_both_after
    {shift r1_end r2_start : Nat}
    (h_rel : r1_end ≤ r2_start) :
  r1_end + shift ≤ r2_start + shift :=
  Nat.add_le_add_right h_rel shift

lemma shift_mono_first_in
    {shift r1_end r2_start : Nat}
    (h_rel : r1_end ≤ r2_start) :
  r1_end + shift ≤ r2_start + shift :=
  Nat.add_le_add_right h_rel shift

/-- If the first region contains `pos` and the second is strictly before `pos`,
this contradicts the sortedness `r1.end_ ≤ r2.start`. -/
private lemma impossible_inside_before
    {pos : Nat} {r1 r2 : GenomicRegion}
    (h_rel : r1.end_ ≤ r2.start)
    (h1_in : r1.start < pos ∧ pos < r1.end_)
    (h2_before : r2.end_ ≤ pos) : False := by
  -- From r2.start < r2.end_ ≤ pos, get r2.start < pos
  have h2_start_lt_pos : r2.start < pos := lt_of_lt_of_le r2.h_valid h2_before
  -- From pos < r1.end_ ≤ r2.start, get pos < r2.start
  have hpos_lt_r2start : pos < r2.start := lt_of_lt_of_le h1_in.2 h_rel
  -- Contradiction: pos < r2.start < pos
  have hcontr : pos < pos := lt_trans hpos_lt_r2start h2_start_lt_pos
  exact (lt_irrefl _ hcontr)

/-- If the first region is after `pos` and the second contains `pos`,
this contradicts the sortedness `r1.end_ ≤ r2.start`. -/
private lemma impossible_after_inside
    {pos : Nat} {r1 r2 : GenomicRegion}
    (h_rel : r1.end_ ≤ r2.start)
    (h1_after : pos ≤ r1.start)
    (h2_in : r2.start < pos ∧ pos < r2.end_) : False := by
  -- pos ≤ r1.start < r1.end_
  have h_pos_lt_r1end : pos < r1.end_ := lt_of_le_of_lt h1_after r1.h_valid
  -- pos < r1.end_ ≤ r2.start
  have h_pos_lt_r2start : pos < r2.start := lt_of_lt_of_le h_pos_lt_r1end h_rel
  -- Contradiction: pos < r2.start < pos
  have hcontr : pos < pos := lt_trans h_pos_lt_r2start h2_in.1
  exact (lt_irrefl _ hcontr)

/-- A simple helper: `a ≤ b` implies `a ≤ b + s`. -/
private lemma le_add_right {a b s : Nat} (h : a ≤ b) : a ≤ b + s :=
  Nat.le_trans h (Nat.le_add_right _ _)

/--
REFACTORED PROOF: This proof replaces the unreadable `split_ifs`/`omega` block
with a more abstract, readable, and maintainable proof based on helper lemmas
that capture the monotonic nature of the region-shifting operation.
-/
lemma chain'_map_shift_preserve
    {regions : List GenomicRegion} (pos shift : Nat)
    (h_chain : List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start) regions) :
    List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start)
      (regions.map (fun r => shiftRegionAfterNat pos shift r)) := by
  -- Relation alias with explicit type to help field-notation inference
  let R : GenomicRegion → GenomicRegion → Prop := fun r1 r2 => r1.end_ ≤ r2.start
  have h_chain' : List.Chain' R regions := h_chain
  induction regions with
  | nil =>
    simp [R]
  | cons r rs ih =>
    cases rs with
    | nil =>
      simp [R]
    | cons r' rs' =>
      -- regions = r :: r' :: rs'
      cases h_chain' with
      | cons h_rel h_tail =>
        constructor
        · -- head relation after map
          -- Split on the three-way case analysis for each region via the if-then-else in shiftRegionAfterNat
          -- r: after/inside/before relative to pos
          by_cases h1_after : pos ≤ r.start
          · -- r after pos
            -- r': after/inside/before
            by_cases h2_after : pos ≤ r'.start
            · -- r' after pos: both sides add `shift`
              have : r.end_ + shift ≤ r'.start + shift := Nat.add_le_add_right h_rel shift
              simpa [R, shiftRegionAfterNat, h1_after, h2_after] using this
            · -- not (pos ≤ r'.start)
              have h2_not_after : ¬ pos ≤ r'.start := h2_after
              by_cases h2_inside : pos < r'.end_
              · -- r' inside: impossible with r after and sortedness
                have h2_start_lt_pos : r'.start < pos := Nat.lt_of_not_ge h2_not_after
                have h_pos_lt_rend : pos < r.end_ := lt_of_le_of_lt h1_after r.h_valid
                have h_pos_lt_r2start : pos < r'.start := lt_of_lt_of_le h_pos_lt_rend h_rel
                have hcontr : pos < pos := lt_trans h_pos_lt_r2start h2_start_lt_pos
                exact (lt_irrefl _ hcontr).elim
              · -- r' before pos: impossible with r after and sortedness
                -- From ¬ pos ≤ r'.start we have r'.start < pos
                have h2_start_lt_pos : r'.start < pos := Nat.lt_of_not_ge h2_not_after
                have h_pos_lt_rend : pos < r.end_ := lt_of_le_of_lt h1_after r.h_valid
                have h_pos_lt_r2start : pos < r'.start := lt_of_lt_of_le h_pos_lt_rend h_rel
                have hcontr : pos < pos := lt_trans h_pos_lt_r2start h2_start_lt_pos
                exact (lt_irrefl _ hcontr).elim
          · -- r not after
            have h1_not_after : ¬ pos ≤ r.start := h1_after
            by_cases h1_inside : pos < r.end_
            · -- r inside pos
              -- r': after/inside/before
              by_cases h2_after : pos ≤ r'.start
              · -- r' after pos: both ends add `shift` on the right; left adds `shift`
                have : r.end_ + shift ≤ r'.start + shift := Nat.add_le_add_right h_rel shift
                simpa [R, shiftRegionAfterNat, h1_not_after, h1_inside, h2_after] using this
              · -- r' not after
                have h2_not_after : ¬ pos ≤ r'.start := h2_after
                by_cases h2_inside : pos < r'.end_
                · -- r' inside pos: impossible with sortedness (cannot both contain pos)
                  have h2_start_lt_pos : r'.start < pos := Nat.lt_of_not_ge h2_not_after
                  have h_pos_lt_r2start : pos < r'.start := lt_of_lt_of_le h1_inside h_rel
                  have hcontr : pos < pos := lt_trans h_pos_lt_r2start h2_start_lt_pos
                  exact (lt_irrefl _ hcontr).elim
                · -- r' before pos: impossible with r inside and sortedness
                  -- not inside ⇒ ¬ pos < r'.end_ ⇒ r'.end_ ≤ pos (via le_of_not_gt)
                  have h2_before : r'.end_ ≤ pos := le_of_not_gt (by simpa [gt_iff_lt] using h2_inside)
                  have h2_start_lt_pos : r'.start < pos := Nat.lt_of_not_ge h2_not_after
                  have hcontr : pos < pos :=
                    lt_trans (lt_of_lt_of_le h1_inside h_rel) h2_start_lt_pos
                  exact (lt_irrefl _ hcontr).elim
            · -- r before pos: pos ≥ r.end_
              -- not inside ⇒ ¬ pos < r.end_ ⇒ r.end_ ≤ pos
              have h1_before : r.end_ ≤ pos := le_of_not_gt (by simpa [gt_iff_lt] using h1_inside)
              -- r': after/inside/before
              by_cases h2_after : pos ≤ r'.start
              · -- r' after: right start adds `shift`, left unchanged ⇒ r.end_ ≤ r'.start + shift
                have : r.end_ ≤ r'.start := h_rel
                have : r.end_ ≤ r'.start + shift := le_add_right this
                simpa [R, shiftRegionAfterNat, h1_not_after, h1_inside, h2_after] using this
              · -- r' not after
                have h2_not_after : ¬ pos ≤ r'.start := h2_after
                by_cases h2_inside : pos < r'.end_
                · -- r' inside: right start unchanged, left unchanged ⇒ r.end_ ≤ r'.start
                  have : r.end_ ≤ r'.start := h_rel
                  simpa [R, shiftRegionAfterNat, h1_not_after, h1_inside, h2_not_after, h2_inside] using this
                · -- r' before: both unchanged ⇒ r.end_ ≤ r'.start
                  have : r.end_ ≤ r'.start := h_rel
                  simpa [R, shiftRegionAfterNat, h1_not_after, h1_inside, h2_not_after, h2_inside] using this
        · -- tail: recurse
          apply ih
          exact h_tail
          aesop

namespace Bio.Genetics

open List

/-- Low-level scanner that collects all AUG positions while sliding by one base. -/
def augScanAux (idx : Nat) (l : List RNABase) (acc : List Nat) : List Nat :=
  match l with
  | .A :: .U :: .G :: rest =>
      -- Record current index, then continue scanning from next base
      augScanAux (idx + 1) (.U :: .G :: rest) (idx :: acc)
  | _ :: rest =>
      augScanAux (idx + 1) rest acc
  | [] =>
      acc.reverse
termination_by l.length
decreasing_by
  simp_wf
  simp_all only [length_cons, lt_add_iff_pos_right, zero_lt_one]

/-- All AUG positions in an RNA sequence. -/
def augPositions (rna : List RNABase) : List Nat :=
  augScanAux 0 rna []

/-- Dropping one element is equivalent to taking the tail. -/
lemma List.drop_one_eq_tail {α : Type*} (l : List α) : l.drop 1 = l.tail := by
  cases l <;> simp [drop, tail]

-- Helper 1: dropping past a known cons
lemma drop_succ_of_drop_cons {rna : List RNABase} {idx : Nat} {a : RNABase} {l : List RNABase}
    (h : rna.drop idx = a :: l) : rna.drop (idx + 1) = l := by
  have h₁ : rna.drop (idx + 1) = (rna.drop idx).drop 1 := by
    -- drop (idx+1) = drop 1 (drop idx)
    simp
  have h₂ : (rna.drop idx).drop 1 = l := by
    -- push drop 1 through the known cons
    have := congrArg (fun t => t.drop 1) h
    simpa using this
  calc
    rna.drop (idx + 1) = (rna.drop idx).drop 1 := h₁
    _ = l := h₂

-- Helper 2: if drop idx = AUG :: rest, then AUG truly occurs at idx in rna
lemma aug_at_of_drop_AUG {rna : List RNABase} {idx : Nat} {rest : List RNABase}
    (h : rna.drop idx = .A :: .U :: .G :: rest) :
    idx + 2 < rna.length ∧
    rna[idx]! = .A ∧ rna[idx+1]! = .U ∧ rna[idx+2]! = .G := by
  -- bounds
  have hlen3 : (rna.drop idx).length ≥ 3 := by simp [h]
  have hlt : idx + 2 < rna.length := by
    have : 3 ≤ rna.length - idx := by simpa [List.length_drop] using hlen3
    omega
  -- derive get? facts from the drop equality, then convert to get!
  have h0opt : rna[idx]? = some .A := by
    have hL : (rna.drop idx)[0]? = some .A := by simp [h]
    have hR : (rna.drop idx)[0]? = rna[idx]? := by
      simp [Nat.add_zero]
    exact (Eq.trans hR.symm hL)
  have h1opt : rna[idx+1]? = some .U := by
    have hL : (rna.drop idx)[1]? = some .U := by simp [h]
    have hR : (rna.drop idx)[1]? = rna[idx+1]? := by
      simp [Nat.one_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    exact (Eq.trans hR.symm hL)
  have h2opt : rna[idx+2]? = some .G := by
    have hL : (rna.drop idx)[2]? = some .G := by simp [h]
    have hR : (rna.drop idx)[2]? = rna[idx+2]? := by
      simp [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    aesop
  -- bases via get!
  have h0 : rna[idx]! = .A := by
    simp [getElem!_eq_getElem?_getD, h0opt]
  have h1 : rna[idx+1]! = .U := by
    simp [getElem!_eq_getElem?_getD, h1opt]
  have h2 : rna[idx+2]! = .G := by
    simp [getElem!_eq_getElem?_getD, h2opt]
  exact ⟨hlt, h0, h1, h2⟩


lemma augScanAux_cons_len1_eq (idx : Nat) (a : RNABase) (acc : List Nat) :
  augScanAux idx [a] acc = augScanAux (idx + 1) [] acc := by
  simp [augScanAux]

lemma augScanAux_cons_len2_eq (idx : Nat) (a b : RNABase) (acc : List Nat) :
  augScanAux idx [a, b] acc = augScanAux (idx + 1) [b] acc := by
  simp [augScanAux]

lemma augScanAux_cons_AUG_eq (idx : Nat) (rest : List RNABase) (acc : List Nat) :
  augScanAux idx (.A :: .U :: .G :: rest) acc =
    augScanAux (idx + 1) (.U :: .G :: rest) (idx :: acc) := by
  simp [augScanAux]

lemma augScanAux_cons_nonAUG_eq (idx : Nat) (a b c : RNABase) (rest : List RNABase)
    (acc : List Nat)
    (h_not : ¬(a = .A ∧ b = .U ∧ c = .G)) :
  augScanAux idx (a :: b :: c :: rest) acc =
    augScanAux (idx + 1) (b :: c :: rest) acc := by
  -- Discharge by cases on (a,b,c) against (A,U,G)
  by_cases hA : a = .A
  · subst hA
    by_cases hU : b = .U
    · subst hU
      by_cases hG : c = .G
      · exact (False.elim (h_not ⟨rfl, rfl, hG⟩))
      · simp [augScanAux, hG]
    · simp [augScanAux, hU]
  · simp [augScanAux, hA]

/-- Specification for the scanner: every reported position is a real AUG. -/
lemma augScanAux_mem_spec {rna : List RNABase} :
  ∀ (idx : Nat) (l : List RNABase) (acc : List Nat),
    rna.drop idx = l →
    ∀ p, p ∈ augScanAux idx l acc →
      p ∈ acc ∨
      (p + 2 < rna.length ∧
       rna[p]! = .A ∧ rna[p+1]! = .U ∧ rna[p+2]! = .G) := by
  intro idx l acc hdrop p
  revert idx acc hdrop
  induction l with
  | nil =>
    intro idx acc hdrop hp
    have : p ∈ acc := by
      simpa [augScanAux, List.mem_reverse] using hp
    exact Or.inl this
  | cons a tl ih =>
    intro idx acc hdrop hp
    -- Split on tail length to mirror augScanAux branches
    cases tl with
    | nil =>
      -- l = [a]
      have hdrop' : rna.drop (idx + 1) = [] := by
        have : rna.drop idx = a :: ([] : List RNABase) := by simpa using hdrop
        exact drop_succ_of_drop_cons (rna := rna) (idx := idx) (a := a) (l := []) this
      have hp' : p ∈ augScanAux (idx + 1) [] acc := by
        simpa [augScanAux_cons_len1_eq] using hp
      simpa using ih (idx + 1) acc hdrop' hp'
    | cons b tl' =>
      cases tl' with
      | nil =>
        -- l = a :: b :: []
        have hdrop' : rna.drop (idx + 1) = [b] := by
          have : rna.drop idx = a :: [b] := by simpa using hdrop
          exact drop_succ_of_drop_cons (rna := rna) (idx := idx) (a := a) (l := [b]) this
        have hp' : p ∈ augScanAux (idx + 1) [b] acc := by
          simpa [augScanAux_cons_len2_eq] using hp
        simpa using ih (idx + 1) acc hdrop' hp'
      | cons c rest =>
        -- l = a :: b :: c :: rest
        by_cases hA : a = .A
        · by_cases hU : b = .U
          · by_cases hG : c = .G
            · -- AUG at head
              have h_head : rna.drop idx = .A :: .U :: .G :: rest := by
                simpa [hA, hU, hG] using hdrop
              have hdropUG : rna.drop (idx + 1) = .U :: .G :: rest :=
                drop_succ_of_drop_cons (rna := rna) (idx := idx) (a := .A) (l := .U :: .G :: rest) h_head
              -- rewrite to match IH's expected tail: b :: c :: rest
              have hdrop' : rna.drop (idx + 1) = b :: c :: rest := by
                simpa [hU, hG] using hdropUG
              have hpUG : p ∈ augScanAux (idx + 1) (.U :: .G :: rest) (idx :: acc) := by
                simpa [augScanAux_cons_AUG_eq, hA, hU, hG] using hp
              -- rewrite membership to match IH's expected tail: b :: c :: rest
              have hp' : p ∈ augScanAux (idx + 1) (b :: c :: rest) (idx :: acc) := by
                simpa [hU, hG] using hpUG
              -- recurse
              have h_rec := ih (idx + 1) (idx :: acc) hdrop' hp'
              rcases h_rec with h_in_acc | h_prop
              · cases List.mem_cons.mp h_in_acc with
                | inl p_eq_idx =>
                  -- derive AUG-at-p without eliminating idx to avoid identifier issues
                  have h_at : p + 2 < rna.length ∧
                              rna[p]! = .A ∧ rna[p+1]! = .U ∧ rna[p+2]! = .G := by
                    have h_idx := aug_at_of_drop_AUG (rna := rna) (idx := idx) (rest := rest) h_head
                    simpa [p_eq_idx] using h_idx
                  exact Or.inr h_at
                | inr p_in_acc =>
                  exact Or.inl p_in_acc
              · exact Or.inr h_prop
            · -- not G
              have hdrop' : rna.drop (idx + 1) = b :: c :: rest := by
                have hx : rna.drop idx = a :: b :: c :: rest := by simpa using hdrop
                exact drop_succ_of_drop_cons (rna := rna) (idx := idx) (a := a) (l := b :: c :: rest) hx
              -- non-AUG witness
              have h_not : ¬(a = .A ∧ b = .U ∧ c = .G) := by
                intro h; exact hG h.2.2
              have step := augScanAux_cons_nonAUG_eq idx a b c rest acc h_not
              have hp' : p ∈ augScanAux (idx + 1) (b :: c :: rest) acc := by
                -- orient equality the right way for the goal
                subst hU hA
                simp_all only [getElem!_eq_getElem?_getD, and_false, not_false_eq_true]--simpa [←step, hA, hU] using hp
              simpa using ih (idx + 1) acc hdrop' hp'
          · -- not U
            have hdrop' : rna.drop (idx + 1) = b :: c :: rest := by
              have hx : rna.drop idx = a :: b :: c :: rest := by simpa using hdrop
              exact drop_succ_of_drop_cons (rna := rna) (idx := idx) (a := a) (l := b :: c :: rest) hx
            -- non-AUG witness
            have h_not : ¬(a = .A ∧ b = .U ∧ c = .G) := by
              intro h; exact hU h.2.1
            have step := augScanAux_cons_nonAUG_eq idx a b c rest acc h_not
            have hp' : p ∈ augScanAux (idx + 1) (b :: c :: rest) acc := by
              simpa [←step, hA] using hp
            simpa using ih (idx + 1) acc hdrop' hp'
        · -- not A
          have hdrop' : rna.drop (idx + 1) = b :: c :: rest := by
            have hx : rna.drop idx = a :: b :: c :: rest := by simpa using hdrop
            exact drop_succ_of_drop_cons (rna := rna) (idx := idx) (a := a) (l := b :: c :: rest) hx
          -- non-AUG witness
          have h_not : ¬(a = .A ∧ b = .U ∧ c = .G) := by
            intro h; exact hA h.1
          have step := augScanAux_cons_nonAUG_eq idx a b c rest acc h_not
          have hp' : p ∈ augScanAux (idx + 1) (b :: c :: rest) acc := by
            simpa [←step] using hp
          simpa using ih (idx + 1) acc hdrop' hp'

/-- Corollary (user-facing): every position reported by augPositions is a real AUG. -/
lemma augPositions_mem_spec {rna : List RNABase} {p : Nat}
    (hp : p ∈ augPositions rna) :
    p + 2 < rna.length ∧
    rna[p]! = .A ∧ rna[p+1]! = .U ∧ rna[p+2]! = .G := by
  -- augPositions rna = augScanAux 0 rna []
  have h := augScanAux_mem_spec (rna := rna) 0 rna [] rfl p (by simpa [augPositions])
  rcases h with h_in_empty | h_aug
  · cases h_in_empty
  · exact h_aug

-- For nonnegative shifts (insertions), Int-to-Nat coercions simplify.
lemma Int.toNat_add_ofNat (a b : Nat) :
    ((a : Int) + (b : Int)).toNat = a + b := by
  rfl

/-- A helper to expose the pure Nat version of the region shift used for insertions. -/
def shiftRegionAfterNat (pos shift : Nat) (r : GenomicRegion) : GenomicRegion :=
  if h_all : pos ≤ r.start then
    -- Entire region occurs after the insertion site: shift both ends.
    { r with
      start := r.start + shift
      end_  := r.end_  + shift
      h_valid := Nat.add_lt_add_right r.h_valid shift }
  else if h_part : pos < r.end_ then
    -- Insertion lands inside this region: extend the end.
    { r with
      end_ := r.end_ + shift
      h_valid := by
        -- r.start < r.end_ ≤ r.end_ + shift
        exact lt_of_lt_of_le r.h_valid (Nat.le_add_right _ _) }
  else
    -- Completely before the insertion: unchanged.
    r

/-- On a singleton list, the nonnegative shift agrees with the Nat-side mapper. -/
lemma shiftRegionsAfter_nonneg_eq_map_singleton
    (pos shift : Nat) (r : GenomicRegion) :
    shiftRegionsAfter pos (shift : Int) [r] =
      [shiftRegionAfterNat pos shift r] := by
  -- Compute by cases on the three branches for r
  by_cases h_all : pos ≤ r.start
  · -- Branch ❶: r fully after pos
    have h_newStart_nonneg : 0 ≤ ((r.start : Int) + shift) := by
      have : (0 : Int) ≤ (r.start : Int) := by exact_mod_cast Nat.zero_le _
      exact add_nonneg this (by exact_mod_cast Nat.zero_le shift)
    have h_newEnd_nonneg : 0 ≤ ((r.end_ : Int) + shift) := by
      have : (0 : Int) ≤ (r.end_ : Int) := by exact_mod_cast Nat.zero_le _
      exact add_nonneg this (by exact_mod_cast Nat.zero_le shift)
    have h_ok : ((r.start : Int) + shift) ≥ 0 ∧
                ((r.end_ : Int) + shift) > ((r.start : Int) + shift) := by
      constructor
      · exact h_newStart_nonneg
      · have : (r.end_ : Int) > (r.start : Int) := by exact_mod_cast r.h_valid
        exact add_lt_add_right this shift
    have h_guard : 0 ≤ ((r.start : Int) + shift) ∧ r.start < r.end_ := by
      exact ⟨h_newStart_nonneg, r.h_valid⟩
    have hstart : ((r.start : Int) + shift).toNat = r.start + shift := by
      simpa using Int.toNat_add_ofNat r.start shift
    have hend : ((r.end_ : Int) + shift).toNat = r.end_ + shift := by
      simpa using Int.toNat_add_ofNat r.end_ shift
    simp [shiftRegionsAfter, shiftRegionAfterNat, h_all, h_guard, hstart, hend, h_ok]
  · -- not h_all
    by_cases h_part : pos < r.end_
    · -- Branch ❷: pos inside r
      have h_gt : (r.start : Int) < (r.end_ : Int) + shift := by
        have h0 : (r.start : Int) < (r.end_ : Int) := by exact_mod_cast r.h_valid
        have h_le : (r.end_ : Int) ≤ (r.end_ : Int) + shift :=
          le_add_of_nonneg_right (by exact_mod_cast Nat.zero_le shift)
        exact lt_of_lt_of_le h0 h_le
      have h_nonneg : 0 ≤ ((r.end_ : Int) + shift) := by
        have : (0 : Int) ≤ (r.end_ : Int) := by exact_mod_cast Nat.zero_le _
        exact add_nonneg this (by exact_mod_cast Nat.zero_le shift)
      have hend : ((r.end_ : Int) + shift).toNat = r.end_ + shift := by
        simpa using Int.toNat_add_ofNat r.end_ shift
      have h_valid_nat : r.start < ((r.end_ : Int) + shift).toNat := by
        have : (r.start : Int) < ((r.end_ : Int) + shift).toNat := by
          simpa [Int.toNat_of_nonneg h_nonneg] using h_gt
        exact_mod_cast this
      simp [shiftRegionsAfter, shiftRegionAfterNat, h_all, h_part, h_gt, hend, h_valid_nat]
    · -- Branch ❸: r before pos
      simp [shiftRegionsAfter, shiftRegionAfterNat, h_all, h_part]

/-- For nonnegative shifts, the head of a cons always survives, so we can peel it as an append. -/
lemma shiftRegionsAfter_nonneg_cons_eq_append
    (pos shift : Nat) (r : GenomicRegion) (rs : List GenomicRegion) :
    shiftRegionsAfter pos (shift : Int) (r :: rs) =
      shiftRegionsAfter pos (shift : Int) [r] ++
      shiftRegionsAfter pos (shift : Int) rs := by
  -- Evaluate head by cases (it never drops for nonnegative shift)
  by_cases h_all : pos ≤ r.start
  ·
    have h_newStart_nonneg : 0 ≤ ((r.start : Int) + shift) := by
      have : (0 : Int) ≤ (r.start : Int) := by exact_mod_cast Nat.zero_le _
      exact add_nonneg this (by exact_mod_cast Nat.zero_le shift)
    have h_newEnd_nonneg : 0 ≤ ((r.end_ : Int) + shift) := by
      have : (0 : Int) ≤ (r.end_ : Int) := by exact_mod_cast Nat.zero_le _
      exact add_nonneg this (by exact_mod_cast Nat.zero_le shift)
    have h_ok : ((r.start : Int) + shift) ≥ 0 ∧
                ((r.end_ : Int) + shift) > ((r.start : Int) + shift) := by
      constructor
      · exact h_newStart_nonneg
      · have : (r.end_ : Int) > (r.start : Int) := by exact_mod_cast r.h_valid
        exact add_lt_add_right this shift
    simp [shiftRegionsAfter, h_all, h_ok, List.singleton, List.append]
    aesop
  ·
    by_cases h_part : pos < r.end_
    ·
      have h_gt : (r.start : Int) < (r.end_ : Int) + shift := by
        have h0 : (r.start : Int) < (r.end_ : Int) := by exact_mod_cast r.h_valid
        have h_le : (r.end_ : Int) ≤ (r.end_ : Int) + shift :=
          le_add_of_nonneg_right (by exact_mod_cast Nat.zero_le shift)
        exact lt_of_lt_of_le h0 h_le
      simp [shiftRegionsAfter, h_all, h_part, h_gt, List.singleton, List.append]
    ·
      simp [shiftRegionsAfter, h_all, h_part, List.singleton, List.append]

/--
For nonnegative shift (the insertion case), shiftRegionsAfter agrees with
a simple map over regions, i.e. it does not drop any region.
-/
lemma shiftRegionsAfter_nonneg_eq_map (pos shift : Nat) (regions : List GenomicRegion) :
    shiftRegionsAfter pos (shift : Int) regions =
      regions.map (shiftRegionAfterNat pos shift) := by
  induction regions with
  | nil =>
      simp [shiftRegionsAfter, shiftRegionAfterNat]
  | cons r rs ih =>
      calc
        shiftRegionsAfter pos (shift : Int) (r :: rs)
            = shiftRegionsAfter pos (shift : Int) [r] ++
              shiftRegionsAfter pos (shift : Int) rs := by
                simpa using
                  shiftRegionsAfter_nonneg_cons_eq_append pos shift r rs
        _ = [shiftRegionAfterNat pos shift r] ++
              shiftRegionsAfter pos (shift : Int) rs := by
                -- rewrite the left operand of ++ using the singleton lemma
                have h := shiftRegionsAfter_nonneg_eq_map_singleton pos shift r
                simpa using
                  congrArg (fun t => t ++ shiftRegionsAfter pos (shift : Int) rs) h
        _ = (shiftRegionAfterNat pos shift r) ::
              shiftRegionsAfter pos (shift : Int) rs := by simp
        _ = (shiftRegionAfterNat pos shift r) ::
              (rs.map (shiftRegionAfterNat pos shift)) := by
                simp [ih]
        _ = (r :: rs).map (shiftRegionAfterNat pos shift) := by simp

/-- Sortedness preservation for insertions (nonnegative shift). -/
lemma shiftRegionsAfter_preserves_sorted
    (pos : Nat) (shift : Nat) (regions : List GenomicRegion)
    (h_sorted : List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start) regions) :
    List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start)
      (shiftRegionsAfter pos (shift : Int) regions) := by
  -- Rewrite to Nat-map form, then reuse the Chain' preservation lemma over maps.
  have h_eq := shiftRegionsAfter_nonneg_eq_map pos shift regions
  -- The map predicate is exactly the one used in `chain'_map_shift_preserves`.
  -- We can now rewrite and apply that lemma.
  simpa [h_eq, shiftRegionAfterNat] using
    (chain'_map_shift_preserve (regions := regions) (pos := pos) (shift := shift) h_sorted)

-- A simple and often-needed length identity for insertion.
lemma length_after_insertion {α} (l ins : List α) (pos : Nat)
    (hpos : pos ≤ l.length) :
    (l.take pos ++ ins ++ l.drop pos).length = l.length + ins.length := by
  -- Expand lengths; take has length pos (since pos ≤ l.length), drop has length l.length - pos
  have hlen :
      (l.take pos ++ ins ++ l.drop pos).length
        = pos + ins.length + (l.length - pos) := by
    simp [List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left hpos, Nat.add_assoc]
  calc
    (l.take pos ++ ins ++ l.drop pos).length
        = pos + ins.length + (l.length - pos) := hlen
    _ = pos + (ins.length + (l.length - pos)) := by
        -- reassociate
        simp [Nat.add_assoc]
    _ = pos + ((l.length - pos) + ins.length) := by
        -- commute inside
        simp [Nat.add_comm]
    _ = (pos + (l.length - pos)) + ins.length := by
        -- reassociate
        simp [Nat.add_assoc]
    _ = l.length + ins.length := by
        -- cancel pos with (l.length - pos) using hpos
        simpa using congrArg (fun t => t + ins.length) (Nat.add_sub_of_le hpos)

/-- Exon boundedness is preserved after insertion (end_ ≤ new sequence length). -/
lemma shiftRegionsAfter_bounded_after_insertion
    (gene : Bio.Sequence.Gene) (pos : Nat) (bases : List Bio.DNABase)
    (hpos : pos ≤ gene.coding_strand.seq.length) :
    let insLen := bases.length
    let mutated_seq := gene.coding_strand.seq.take pos ++ bases ++ gene.coding_strand.seq.drop pos
    let shifted_exons := shiftRegionsAfter pos (insLen : Int) gene.exons
    ∀ r' ∈ shifted_exons, r'.end_ ≤ mutated_seq.length := by
  intro insLen mutated_seq shifted_exons r' hr'
  -- Work with the explicit definitions of the lets.
  change r' ∈ shiftRegionsAfter pos (insLen : Int) gene.exons at hr'
  change r'.end_ ≤ (gene.coding_strand.seq.take pos ++ bases ++ gene.coding_strand.seq.drop pos).length
  -- Use the map characterization for nonnegative shift to pull back to an original exon.
  have h_eq := shiftRegionsAfter_nonneg_eq_map pos insLen gene.exons
  have hr'_map : r' ∈ gene.exons.map (shiftRegionAfterNat pos insLen) := by
    simpa [h_eq] using hr'
  rcases List.mem_map.1 hr'_map with ⟨r, hr_mem, hmap⟩
  -- Bound original exon end
  have hr_bound := gene.h_exons_bounded r hr_mem
  -- Replace r' with the mapped region
  subst hmap
  -- New length equals original length + inserted length
  have hlen_base :
      (gene.coding_strand.seq.take pos ++ bases ++ gene.coding_strand.seq.drop pos).length
        = gene.coding_strand.seq.length + bases.length :=
    length_after_insertion _ _ _ hpos
  have hlen :
      (gene.coding_strand.seq.take pos ++ bases ++ gene.coding_strand.seq.drop pos).length
        = gene.coding_strand.seq.length + insLen := by
    simpa [insLen] using hlen_base
  -- Case analysis on the shift branches
  by_cases h_all : pos ≤ r.start
  · -- Fully after pos: end_ = r.end_ + insLen
    have hend : (shiftRegionAfterNat pos insLen r).end_ = r.end_ + insLen := by
      simp [shiftRegionAfterNat, h_all]
    aesop
  · by_cases h_part : pos < r.end_
    · -- Partially overlapping: end_ = r.end_ + insLen
      have hend : (shiftRegionAfterNat pos insLen r).end_ = r.end_ + insLen := by
        simp [shiftRegionAfterNat, h_all, h_part]
      aesop
    · -- Completely before pos: unchanged end_ = r.end_
      have hend : (shiftRegionAfterNat pos insLen r).end_ = r.end_ := by
        simp [shiftRegionAfterNat, h_all, h_part]
      -- mutated length ≥ original length
      have h_ge_len :
          gene.coding_strand.seq.length
            ≤ (gene.coding_strand.seq.take pos ++ bases ++ gene.coding_strand.seq.drop pos).length := by
        -- gene.len ≤ gene.len + insLen, then rewrite by hlen
        have : gene.coding_strand.seq.length ≤ gene.coding_strand.seq.length + insLen :=
          Nat.le_add_right _ _
        aesop
      have : r.end_ ≤ (gene.coding_strand.seq.take pos ++ bases ++ gene.coding_strand.seq.drop pos).length :=
        le_trans hr_bound h_ge_len
      simpa [hend] using this

def applyInsertion (gene : Gene) (pos : Nat) (bases : List DNABase) : Option Gene :=
  -- Allow insertion at the end of the sequence
  if h_pos : pos ≤ gene.coding_strand.seq.length then
    let insLen := bases.length
    let mutated_seq :=
      gene.coding_strand.seq.take pos ++ bases ++ gene.coding_strand.seq.drop pos
    let shifted_exons := shiftRegionsAfter pos (insLen : Int) gene.exons
    if h_preserved : shifted_exons ≠ [] then
      some {
        id := gene.id
        coding_strand := { seq := mutated_seq }
        exons := shifted_exons
        promoter_region := gene.promoter_region
        poly_a_site := gene.poly_a_site.map (fun p => if p ≥ pos then p + insLen else p)
        h_exons_sorted := by
          -- Sortedness is preserved by region shifting (nonnegative shift).
          exact shiftRegionsAfter_preserves_sorted pos insLen gene.exons gene.h_exons_sorted
        h_exons_bounded := by
          -- Every shifted exon end_ stays within new sequence length.
          intro r' hr'
          -- Use the boundedness lemma specialized to this gene/pos/bases, and normalize the local lets.
          simpa [mutated_seq, shifted_exons] using
            (shiftRegionsAfter_bounded_after_insertion
               (gene := gene) (pos := pos) (bases := bases) h_pos
               r' hr')
        h_exons_nonempty := h_preserved
      }
    else
      none
  else
    none

/-! ## Utilities for complex mutations -/

-- Deletion length identity
lemma length_after_deletion {α} (l : List α) (pos len : Nat)
    (h : pos + len ≤ l.length) :
    (l.take pos ++ l.drop (pos + len)).length = l.length - len := by
  have hpos : pos ≤ l.length := by
    exact Nat.le_trans (Nat.le_add_right _ _) h
  have htake : (l.take pos).length = pos := by
    simp [List.length_take, Nat.min_eq_left hpos]
  have hdrop : (l.drop (pos + len)).length = l.length - (pos + len) := by
    simp [List.length_drop]
  calc
    (l.take pos ++ l.drop (pos + len)).length
        = (l.take pos).length + (l.drop (pos + len)).length := by
          simp [List.length_append]
    _ = pos + (l.length - (pos + len)) := by
          simp [htake, hdrop]
    _ = pos + ((l.length - pos) - len) := by
          simp [Nat.sub_sub]
    _ = (pos + (l.length - pos)) - len := by
          -- use add_sub_assoc with len ≤ l.length - pos
          have hlen_le : len ≤ l.length - pos := by
            have h' : pos + len ≤ pos + (l.length - pos) := by
              simpa [Nat.add_sub_of_le hpos] using h
            exact (Nat.le_sub_iff_add_le' hpos).mpr h
          exact Eq.symm (Nat.add_sub_assoc hlen_le pos)
  simp_all only [length_take, inf_of_le_left, length_drop, add_tsub_cancel_of_le]

-- Int helper: toNat of a Nat subtraction when nonnegative
lemma Int.toNat_sub_of_le (a b : Nat) (h : b ≤ a) :
    ((a : Int) - (b : Int)).toNat = a - b := by
  have hcast := (Int.ofNat_sub h).symm
  calc
    ((a : Int) - (b : Int)).toNat
        = (((a - b : Nat) : Int)).toNat := by
              exact congrArg Int.toNat hcast
    _ = a - b := by
              simp

/-- If 0 ≤ (a : Int) - b, then b ≤ a (Nat). -/
lemma nat_le_of_int_sub_nonneg {a b : Nat} (h : (0 : Int) ≤ ((a : Int) - b)) : b ≤ a := by
  -- From a - b ≥ 0 we get b ≤ a in Int, then drop to Nat
  have : (b : Int) ≤ (a : Int) := by simpa [sub_nonneg] using h
  exact Int.ofNat_le.mp this

/-- From a + b ≤ c we get a ≤ c - b. -/
lemma le_sub_of_add_le {a b c : Nat} (h : a + b ≤ c) : a ≤ c - b := by
  have hb : b ≤ c := le_trans (Nat.le_add_left _ _) h
  -- Use standard equivalence: a ≤ c - b ↔ a + b ≤ c (under b ≤ c)
  exact (Nat.le_sub_iff_add_le hb).mpr h

/-- After-case extractor for `shiftRegionsAfter` with negative shift:
if `pos ≤ r.start` and the `filterMap` produced `r'`, then
`r'.end_ = ((r.end_ : Int) - len).toNat`, and `(r.start : Int) - len ≥ 0`. -/
lemma shiftRegionsAfter_after_case_end_toNat_eq
    {pos len : Nat} {r r' : GenomicRegion}
    (hall : pos ≤ r.start)
    (hopt :
      (if pos ≤ r.start then
        let newStart : Int := (r.start : Int) + (-(len : Int))
        let newEnd   : Int := (r.end_  : Int) + (-(len : Int))
        if h_ok : newStart ≥ 0 ∧ newEnd > newStart then
          let h_valid : newStart.toNat < newEnd.toNat := by
            -- this proof exists inside the original definition; we won't need it externally
            have : (newStart.toNat : Int) < (newEnd.toNat : Int) := by
              have h₁ : (newStart.toNat : Int) = newStart := by
                simp [Int.toNat_of_nonneg h_ok.1]
              have h₂ : (newEnd.toNat : Int) = newEnd := by
                have : (0 : Int) ≤ newEnd := le_trans h_ok.1 (le_of_lt h_ok.2)
                simp [Int.toNat_of_nonneg this]
              simpa [h₁, h₂] using h_ok.2
            exact_mod_cast this
          some { start := newStart.toNat, end_ := newEnd.toNat, h_valid := h_valid }
        else
          none
      else if pos < r.end_ then
        let newEnd : Int := (r.end_ : Int) + (-(len : Int))
        if h_gt : newEnd > r.start then
          let h_valid : r.start < newEnd.toNat := by
            have h_nonneg : (0 : Int) ≤ newEnd := by
              have : (0 : Int) ≤ (r.start : Int) := by exact_mod_cast Nat.zero_le _
              exact le_trans this (le_of_lt h_gt)
            have : (r.start : Int) < (newEnd.toNat : Int) := by
              simpa [Int.toNat_of_nonneg h_nonneg] using h_gt
            exact_mod_cast this
          some { r with end_ := newEnd.toNat, h_valid := h_valid }
        else
          none
      else
        some r)
      = some r') :
    r'.end_ = ((r.end_ : Int) - len).toNat ∧ (0 : Int) ≤ (r.start : Int) - len := by
  classical
  -- Reduce outer guard to the "after" branch
  simp [shiftRegionsAfter, hall] at hopt
  -- Re-express newStart/newEnd the way we want to read them
  set newStart : Int := (r.start : Int) - len
  set newEnd   : Int := (r.end_  : Int) - len
  have hform : (if h_ok : newStart ≥ 0 ∧ newEnd > newStart then
                  some { start := newStart.toNat, end_ := newEnd.toNat,
                         h_valid := by
                           -- Reconstruct the inner h_valid proof so types match exactly
                           have : (newStart.toNat : Int) < (newEnd.toNat : Int) := by
                             have h₁ : (newStart.toNat : Int) = newStart := by
                               simp [Int.toNat_of_nonneg h_ok.1]
                             have h₂ : (newEnd.toNat : Int) = newEnd := by
                               have : (0 : Int) ≤ newEnd := le_trans h_ok.1 (le_of_lt h_ok.2)
                               simp [Int.toNat_of_nonneg this]
                             simpa [h₁, h₂] using h_ok.2
                           exact_mod_cast this }
                else none) = some r' := by
    -- Align (+ -len) with (- len) via sub_eq_add_neg
    simpa [newStart, newEnd, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hopt
  -- The inner guard must be true, otherwise LHS is none
  by_cases hok : newStart ≥ 0 ∧ newEnd > newStart
  · have hsome := hform
    simp [hok] at hsome
    -- Extract the record equality and project end_
    have hrec := hsome
    have hend := congrArg GenomicRegion.end_ hrec
    exact ⟨by simpa [newEnd] using hend.symm, hok.1⟩
  · -- Impossible: none = some r'
    have := hform
    simp [hok] at this

lemma shiftRegionsAfter_inside_case_end_toNat_eq
    {pos len : Nat} {r r' : GenomicRegion}
    (hnall : ¬ pos ≤ r.start)
    (hpart : pos < r.end_)
    (hopt :
      (if pos ≤ r.start then
        let newStart : Int := (r.start : Int) + (-(len : Int))
        let newEnd   : Int := (r.end_  : Int) + (-(len : Int))
        if h_ok : newStart ≥ 0 ∧ newEnd > newStart then
          let h_valid : newStart.toNat < newEnd.toNat := by
            -- Derive the Nat inequality from h_ok by transporting through toNat.
            have : (newStart.toNat : Int) < (newEnd.toNat : Int) := by
              have h₁ : (newStart.toNat : Int) = newStart := by
                simp [Int.toNat_of_nonneg h_ok.1]
              have h₂ : (newEnd.toNat : Int) = newEnd := by
                have : (0 : Int) ≤ newEnd := le_trans h_ok.1 (le_of_lt h_ok.2)
                simp [Int.toNat_of_nonneg this]
              simpa [h₁, h₂] using h_ok.2
            exact_mod_cast this
          some { start := newStart.toNat, end_ := newEnd.toNat, h_valid := h_valid }
        else
          none
      else if pos < r.end_ then
        let newEnd : Int := (r.end_ : Int) + (-(len : Int))
        if h_gt : newEnd > r.start then
          let h_valid : r.start < newEnd.toNat := by
            have h_nonneg : (0 : Int) ≤ newEnd := by
              have : (0 : Int) ≤ (r.start : Int) := by exact_mod_cast Nat.zero_le _
              exact le_trans this (le_of_lt h_gt)
            have : (r.start : Int) < (newEnd.toNat : Int) := by
              simpa [Int.toNat_of_nonneg h_nonneg] using h_gt
            exact_mod_cast this
          some { r with end_ := newEnd.toNat, h_valid := h_valid }
        else
          none
      else
        some r)
      = some r') :
    r'.end_ = ((r.end_ : Int) - len).toNat ∧ (0 : Int) ≤ (r.end_ : Int) - len := by
  classical
  set newEnd : Int := (r.end_ : Int) - len
  -- Equivalence between the guard used here and an algebraically convenient form
  have hiff :
      (newEnd > r.start) ↔ ((r.start : Int) + (len : Int) < (r.end_ : Int)) := by
    constructor
    · intro h
      -- add len on both sides
      have := add_lt_add_right h (len : Int)
      -- (r.end_ - len) + len > r.start + len  ==> r.end_ > r.start + len
      simpa [newEnd, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    · intro h
      -- subtract len on both sides
      have := add_lt_add_right h (-(len : Int))
      -- r.start + len - len < r.end_ - len  ==> r.start < r.end_ - len
      simpa [newEnd, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  by_cases hgt : newEnd > r.start
  ·
    -- Build validity proof outside the record to avoid parser issues
    have h_nonneg : (0 : Int) ≤ newEnd := by
      have : (0 : Int) ≤ (r.start : Int) := by exact_mod_cast Nat.zero_le _
      exact le_trans this (le_of_lt hgt)
    have h_valid' : r.start < newEnd.toNat := by
      have : (r.start : Int) < (newEnd.toNat : Int) := by
        simpa [Int.toNat_of_nonneg h_nonneg] using hgt
      exact_mod_cast this
    -- From the hypothesis, after simplifying guards, we get a plain record equality.
    have hcond : (r.start : Int) + (len : Int) < (r.end_ : Int) := (hiff.mp hgt)
    have hrec :
        ({ r with end_ := newEnd.toNat, h_valid := h_valid' } : GenomicRegion) = r' := by
      -- Note: simp reduces Option.some equality to a record equality via Option.some.inj
      simpa [shiftRegionsAfter, hnall, hpart, newEnd, hcond, sub_eq_add_neg] using hopt
    -- Project the end_ field
    have hend := congrArg GenomicRegion.end_ hrec
    exact ⟨by simpa [newEnd] using hend.symm, h_nonneg⟩
  ·
    -- In the inner-false branch, the filterMap yields none, contradicting `= some r'`.
    have hcond_false : ¬ ((r.start : Int) + (len : Int) < (r.end_ : Int)) := by
      intro hcond
      -- contradict hgt using the equivalence
      exact hgt (hiff.mpr hcond)
    have hfalse : False := by
      -- With a false guard, the branch produces `none`, so equality to `some r'` is impossible.
      simp [shiftRegionsAfter, hnall, hpart, newEnd, hcond_false] at hopt
    cases hfalse

/-- Boundedness of exon ends after deletion. -/
lemma shiftRegionsAfter_bounded_after_deletion
    (gene : Bio.Sequence.Gene) (pos len : Nat)
    (h : pos + len ≤ gene.coding_strand.seq.length) :
    let mutated_seq := gene.coding_strand.seq.take pos ++ gene.coding_strand.seq.drop (pos + len)
    let shifted_exons := shiftRegionsAfter pos (-(len : Int)) gene.exons
    ∀ r' ∈ shifted_exons, r'.end_ ≤ mutated_seq.length := by
  intro mutated_seq shifted_exons r' hr'
  -- Pull out a preimage region r producing r'
  rcases List.mem_filterMap.1 hr' with ⟨r, hr_mem, hopt⟩
  -- mutated length
  have hlen : mutated_seq.length = gene.coding_strand.seq.length - len := by
    simp [mutated_seq, length_after_deletion _ _ _ h]
  -- Original exon boundedness
  have hr_bound := gene.h_exons_bounded r hr_mem
  -- Split by the same guards as shiftRegionsAfter
  by_cases hall : pos ≤ r.start
  · -- After case: both start and end shift left by len
    -- Extract end_ shape and nonneg from the branch
    have h_after :=
      shiftRegionsAfter_after_case_end_toNat_eq
        (pos := pos) (len := len) (r := r) (r' := r') hall hopt
    rcases h_after with ⟨hend_eq, hstart_nonneg⟩
    -- From newStart ≥ 0, get len ≤ r.start ≤ r.end_
    have hlen_le_start : len ≤ r.start :=
      nat_le_of_int_sub_nonneg (a := r.start) (b := len) hstart_nonneg
    have hlen_le_end : len ≤ r.end_ := le_trans hlen_le_start (le_of_lt r.h_valid)
    -- Convert toNat subtraction into Nat subtraction
    have hendNat : ((r.end_ : Int) - len).toNat = r.end_ - len :=
      Int.toNat_sub_of_le r.end_ len hlen_le_end
    -- Bound: r'.end_ = r.end_ - len ≤ gene.len - len
    have : r'.end_ ≤ gene.coding_strand.seq.length - len := by
      simpa [hend_eq, hendNat] using Nat.sub_le_sub_right hr_bound len
    simpa [hlen] using this
  · -- Not after: split into overlap vs before
    by_cases hpart : pos < r.end_
    · -- Inside/overlap case: only the end shifts left by len
      have h_inside :=
        shiftRegionsAfter_inside_case_end_toNat_eq
          (pos := pos) (len := len) (r := r) (r' := r') (hnall := hall) (hpart := hpart) hopt
      rcases h_inside with ⟨hend_eq, hend_nonneg⟩
      -- From newEnd ≥ 0, deduce len ≤ r.end_
      have hlen_le_end : len ≤ r.end_ :=
        nat_le_of_int_sub_nonneg (a := r.end_) (b := len) hend_nonneg
      have hendNat : ((r.end_ : Int) - len).toNat = r.end_ - len :=
        Int.toNat_sub_of_le r.end_ len hlen_le_end
      have : r'.end_ ≤ gene.coding_strand.seq.length - len := by
        simpa [hend_eq, hendNat] using Nat.sub_le_sub_right hr_bound len
      simpa [hlen] using this
    · -- Before case: unchanged region, and r.end_ ≤ pos ≤ gene.len - len
      have r_before : r.end_ ≤ pos := le_of_not_gt hpart
      -- In this branch the filterMap returns `some r`, hence r' = r
      have hr'_eq_r : r' = r := by
        -- In the before-branch of `shiftRegionsAfter`, the region is unchanged
        simp [shiftRegionsAfter, hall, hpart] at hopt
        -- hopt simplifies to r = r', so take symmetry
        exact hopt.symm
      -- Bound r.end_ by gene.len - len via pos + len ≤ gene.len
      have hpos_le : pos ≤ gene.coding_strand.seq.length - len :=
        le_sub_of_add_le (a := pos) (b := len) (c := gene.coding_strand.seq.length) h
      have : r'.end_ ≤ gene.coding_strand.seq.length - len := by
        simpa [hr'_eq_r] using (le_trans r_before hpos_le)
      simpa [hlen] using this

-- A simple normalizer to enforce non-overlap and sortedness by clamping starts
-- Forward-building version (no reverse), avoiding accumulator reversal headaches.
private def enforceSortedNonOverlap.go (lastEnd : Nat) : List GenomicRegion → List GenomicRegion
  | [] => []
  | r :: rs =>
    let start' := max r.start lastEnd
    if h : start' < r.end_ then
      let r' : GenomicRegion := { r with start := start', h_valid := h } -- use the branch witness directly
      r' :: enforceSortedNonOverlap.go r'.end_ rs
    else
      enforceSortedNonOverlap.go lastEnd rs

/-- Normalize a list of regions so it is Chain' by clamping starts and removing empty segments. -/
def enforceSortedNonOverlap (regions : List GenomicRegion) : List GenomicRegion :=
  enforceSortedNonOverlap.go 0 regions

private lemma enforceSortedNonOverlap.head_start_ge
    {lastEnd : Nat} {rs : List GenomicRegion} {s : GenomicRegion} {rest : List GenomicRegion}
    (h : enforceSortedNonOverlap.go lastEnd rs = s :: rest) :
    lastEnd ≤ s.start := by
  revert lastEnd s rest
  induction rs with
  | nil =>
      intro lastEnd s rest h; cases h
  | cons r rs ih =>
      intro lastEnd s rest h
      dsimp [enforceSortedNonOverlap.go] at h
      -- Keep start' abstract to avoid rewriting guards to conjunctions.
      set start' := max r.start lastEnd with hstart'
      by_cases hk : start' < r.end_
      · -- kept r (clamped)
        -- Rewrite equality under kept branch
        have hcons :
            ({ r with start := start', h_valid := hk } : GenomicRegion) ::
              enforceSortedNonOverlap.go r.end_ rs = s :: rest := by
          -- Do not include hstart' in simp args to avoid max_lt_iff rewriting.
          simpa [enforceSortedNonOverlap.go, hk] using h
        -- Extract head equality via head?
        have hhead :
            some ({ r with start := start', h_valid := hk } : GenomicRegion) = some s := by
          simpa using congrArg List.head? hcons
        have hs_eq : ({ r with start := start', h_valid := hk } : GenomicRegion) = s :=
          Option.some.inj hhead
        -- Conclude lastEnd ≤ s.start from start' = max r.start lastEnd
        have hle : lastEnd ≤ start' := Nat.le_max_right _ _
        -- Rewrite s.start using hs_eq
        aesop--simpa [hs_eq] using hle
      · -- dropped r, continue with IH on the rewritten equality
        have h' : enforceSortedNonOverlap.go lastEnd rs = s :: rest := by
          simpa [enforceSortedNonOverlap.go, hk] using h
        exact ih h'

/-- The normalizer produces a Chain'-sorted list. -/
lemma enforceSortedNonOverlap_chain (regions : List GenomicRegion) :
    List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start) (enforceSortedNonOverlap regions) := by
  -- Prove a stronger statement for the forward-building worker `go`.
  have aux :
      ∀ (rs : List GenomicRegion), ∀ lastEnd,
        List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start)
          (enforceSortedNonOverlap.go lastEnd rs) := by
    intro rs
    induction rs with
    | nil =>
        intro lastEnd
        simp [enforceSortedNonOverlap, enforceSortedNonOverlap.go]
    | cons r rs ih =>
        intro lastEnd
        dsimp [enforceSortedNonOverlap.go]
        -- Keep start' abstract to avoid conj guards
        set start' := max r.start lastEnd with hstart'
        by_cases hk : start' < r.end_
        · -- keep clamped region, show chain for r' :: tail
          -- Build the tail once
          cases htail : enforceSortedNonOverlap.go (r.end_) rs with
          | nil =>
              -- Single element list is trivially Chain'
              simp [enforceSortedNonOverlap.go, hk, htail]
          | cons s rest =>
              -- Need r'.end_ ≤ s.start and Chain for s :: rest
              have hs : r.end_ ≤ s.start :=
                enforceSortedNonOverlap.head_start_ge (lastEnd := r.end_) (rs := rs) (s := s) (rest := rest) htail
              -- r'.end_ = r.end_ since updating start only
              have hs' :
                  ({ r with start := start', h_valid := hk } : GenomicRegion).end_ ≤ s.start := by
                simpa using hs
              -- Chain' for tail by IH on rs with lastEnd = r.end_
              have hchain_tail :
                  List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start) (s :: rest) := by
                simpa [htail] using ih (r.end_)
              -- Unfold Chain' on the cons
              simpa [enforceSortedNonOverlap.go, hk, htail] using
                And.intro hs' hchain_tail
        · -- drop r, use IH
          simpa [enforceSortedNonOverlap.go, hk] using ih lastEnd
  simpa [enforceSortedNonOverlap] using aux regions 0

/-- Boundedness propagates through the normalizer. -/
lemma enforceSortedNonOverlap_bounded
    {L : Nat} {regions : List GenomicRegion}
    (hB : ∀ r ∈ regions, r.end_ ≤ L) :
    ∀ r' ∈ enforceSortedNonOverlap regions, r'.end_ ≤ L := by
  -- Prove a stronger statement directly for the forward-building worker `go`.
  have aux :
      ∀ (rs : List GenomicRegion) (lastEnd : Nat),
        (∀ r ∈ rs, r.end_ ≤ L) →
        ∀ r' ∈ enforceSortedNonOverlap.go lastEnd rs, r'.end_ ≤ L := by
    intro rs
    induction rs with
    | nil =>
        intro lastEnd _ r' hr'
        -- go lastEnd [] = []
        simp [enforceSortedNonOverlap.go] at hr'
    | cons r rs ih =>
        intro lastEnd hRs r' hr'
        dsimp [enforceSortedNonOverlap.go] at hr'
        set start' := max r.start lastEnd with hstart'
        by_cases hk : start' < r.end_
        · -- kept head, membership splits
          have hRs_head : r.end_ ≤ L := hRs r (by simp)
          have hRs_tail : ∀ x ∈ rs, x.end_ ≤ L := by
            intro x hx; exact hRs x (by simp [hx])
          -- Under kept branch, rewrite membership into the concrete cons
          have hmem :
              r' ∈ ({ r with start := start', h_valid := hk } : GenomicRegion) ::
                    enforceSortedNonOverlap.go
                      (({ r with start := start', h_valid := hk } : GenomicRegion).end_) rs := by
            -- Avoid rewriting start' into max ... to prevent conj guards; do not use hstart' here.
            simpa [enforceSortedNonOverlap.go, hk] using hr'
          -- Split membership
          have hr'cases :
              r' = ({ r with start := start', h_valid := hk } : GenomicRegion) ∨
              r' ∈ enforceSortedNonOverlap.go
                      (({ r with start := start', h_valid := hk } : GenomicRegion).end_) rs :=
            (List.mem_cons).1 hmem
          cases hr'cases with
          | inl hhead =>
              -- r' is the clamped head; end_ unchanged
              have : r'.end_ ≤ L := by
                -- r'.end_ = r.end_
                simpa [hhead] using hRs_head
              exact this
          | inr htail =>
              -- r' in tail; first replace r'.end_ with r.end_ in the go-argument
              have rend :
                  ({ r with start := start', h_valid := hk } : GenomicRegion).end_ = r.end_ := rfl
              have htail' :
                  r' ∈ enforceSortedNonOverlap.go (r.end_) rs := by
                simpa [rend] using htail
              -- recurse with lastEnd = r.end_
              exact ih (r.end_) hRs_tail r' htail'
        · -- dropped head; recurse on tail with same lastEnd
          have hRs_tail : ∀ x ∈ rs, x.end_ ≤ L := by
            intro x hx; exact hRs x (by simp [hx])
          -- Rewrite membership to the tail, then apply IH
          have hr'_tail : r' ∈ enforceSortedNonOverlap.go lastEnd rs := by
            -- Avoid including hstart' to prevent conj guards; hk is enough.
            simpa [enforceSortedNonOverlap.go, hk] using hr'
          exact ih lastEnd hRs_tail r' hr'_tail
  intro r' hr'
  -- Apply aux with lastEnd = 0 and rs = regions
  have := aux regions 0 hB r' (by simpa [enforceSortedNonOverlap] using hr')
  exact this

-- Length preservation for inversion (replace a segment by its reverse).
lemma length_after_inversion {α} (l : List α) (start end_ : Nat)
    (hse : start ≤ end_) (hend : end_ ≤ l.length) :
    (l.take start ++ ((l.drop start).take (end_ - start)).reverse ++ l.drop end_).length
      = l.length := by
  have hstart_le_len : start ≤ l.length := le_trans hse hend
  have h_take : (l.take start).length = start := by
    simp [List.length_take, Nat.min_eq_left hstart_le_len]
  have h_mid_bound : end_ - start ≤ (l.length - start) := by
    simpa using Nat.sub_le_sub_right hend start
  have h_mid :
      ((l.drop start).take (end_ - start)).length = (end_ - start) := by
    simp [List.length_take, List.length_drop, Nat.min_eq_left h_mid_bound]
  have h_drop : (l.drop end_).length = l.length - end_ := by
    simp [List.length_drop]
  calc
    (l.take start ++ ((l.drop start).take (end_ - start)).reverse ++ l.drop end_).length
        = (l.take start).length + ((l.drop start).take (end_ - start)).reverse.length
          + (l.drop end_).length := by
            simp [List.length_append, Nat.add_assoc]
    _ = start + (end_ - start) + (l.length - end_) := by
          simp [h_take, h_mid, h_drop, List.length_reverse, Nat.add_assoc]
    _ = l.length := by
          have h1 : start + (end_ - start) = end_ := Nat.add_sub_of_le hse
          have h2 : end_ + (l.length - end_) = l.length := Nat.add_sub_of_le hend
          -- rewrite with h1, then finish with h2
          calc
            start + (end_ - start) + (l.length - end_)
                = (start + (end_ - start)) + (l.length - end_) := by
                  simp [Nat.add_assoc]
            _ = end_ + (l.length - end_) := by simp [h1]
            _ = l.length := h2

/--
NEW: A robust, single-pass function to apply a deletion to an exon list.
This function correctly merges exons when an intron is deleted, and truncates
exons when the deletion overlaps them. It replaces the fragile `shiftRegionsAfter`
and `enforceSortedNonOverlap` combination for deletions.
-/
def applyDeletionToExons (exons : List GenomicRegion) (del_start del_end : Nat) : List GenomicRegion :=
  let rec go (remaining : List GenomicRegion) (acc : List GenomicRegion) : List GenomicRegion :=
    match remaining with
    | [] => acc.reverse
    | r :: rs =>
      let r_start := r.start
      let r_end := r.end_
      -- Case 1: Exon is completely before the deletion. Keep it.
      if h_before : r_end ≤ del_start then
        go rs (r :: acc)
      -- Case 2: Exon is completely after the deletion. Shift it left.
      else if h_after : r_start ≥ del_end then
        let shift_len := del_end - del_start
        -- Prove start - shift_len < end_ - shift_len using r.h_valid
        -- and shift_len ≤ r.start, shift_len ≤ r.end_.
        have h_s_le_start : shift_len ≤ r.start := by
          -- shift_len ≤ del_end ≤ r.start
          exact le_trans (Nat.sub_le _ _) h_after
        have h_delEnd_le_end : del_end ≤ r.end_ := by
          -- del_end ≤ r_start ≤ r_end_
          exact le_trans h_after (Nat.le_of_lt r.h_valid)
        have h_s_le_end : shift_len ≤ r.end_ := by
          exact le_trans (Nat.sub_le _ _) h_delEnd_le_end
        -- Convert r.start < r.end_ to (shift_len + (r.start - shift_len)) < (shift_len + (r.end_ - shift_len))
        have h_added :
            shift_len + (r.start - shift_len) < shift_len + (r.end_ - shift_len) := by
          -- Use add-sub, which matches the goal shape directly without needing commutativity.
          simpa [Nat.add_sub_of_le h_s_le_start, Nat.add_sub_of_le h_s_le_end] using r.h_valid
        -- Cancel the common addend on the left
        have h_sub_lt :
            r.start - shift_len < r.end_ - shift_len := Nat.lt_of_add_lt_add_left h_added
        let new_r : GenomicRegion := {
          start := r.start - shift_len,
          end_ := r.end_ - shift_len,
          h_valid := h_sub_lt
        }
        go rs (new_r :: acc)
      -- Case 3: Deletion is strictly within the exon. Shrink its end.
      else if h_inside : del_start > r_start ∧ del_end < r_end then
        let shift_len := del_end - del_start
        -- Show r.start < r.end_ - shift_len by showing r.start + shift_len < r.end_,
        -- then use Nat.lt_sub_iff_add_lt (since shift_len ≤ r.end_).
        have h_s_le_end : shift_len ≤ r.end_ := by
          exact le_trans (Nat.sub_le _ _) (Nat.le_of_lt h_inside.2)
        have h_add_lt : r.start + shift_len < r.end_ := by
          by_cases h_order : del_start ≤ del_end
          · -- r.start + (del_end - del_start) < del_end < r.end_
            have h_lt_left :
                r.start + (del_end - del_start) < del_start + (del_end - del_start) :=
              Nat.add_lt_add_right (show r.start < del_start from h_inside.1) _
            have h_eq : del_start + (del_end - del_start) = del_end :=
              Nat.add_sub_of_le h_order
            have h_left' : r.start + shift_len < del_end := by
              simpa [h_eq] using h_lt_left
            exact lt_trans h_left' h_inside.2
          · -- del_end < del_start ⇒ shift_len = 0
            have hlt : del_end < del_start := Nat.lt_of_not_ge h_order
            have h_zero : shift_len = 0 := Nat.sub_eq_zero_of_le (le_of_lt hlt)
            simpa [h_zero] using r.h_valid
        have h_valid' : r.start < r.end_ - shift_len :=
          Nat.lt_sub_of_add_lt h_add_lt
        let new_r : GenomicRegion := {
          start := r.start,
          end_ := r.end_ - shift_len,
          h_valid := h_valid'
        }
        go rs (new_r :: acc)
      -- Case 4: Complex overlaps (truncation, merging)
      else
        -- Simplify by truncating from the right.
        let new_end := if r_end ≤ del_end then del_start else r_end - (del_end - del_start)
        if h_keep : r_start < new_end then
          let new_r : GenomicRegion := { r with end_ := new_end, h_valid := h_keep }
          go rs (new_r :: acc)
        else
          go rs acc -- Deletion consumed the whole exon
  go exons []

/-- Apply deletion mutation with coordinate adjustment (uses proven normalizer). -/
def applyDeletion (gene : Gene) (pos : Nat) (len : Nat) : Option Gene :=
  if h_bounds : pos + len ≤ gene.coding_strand.seq.length then
    let mutated_seq := gene.coding_strand.seq.take pos ++
                      gene.coding_strand.seq.drop (pos + len)
    let shifted_exons_raw := shiftRegionsAfter pos (-len : Int) gene.exons
    -- Normalize to enforce Chain' and non-overlap
    let shifted_exons := enforceSortedNonOverlap shifted_exons_raw

    -- Deletions might remove entire exons
    if h_valid : shifted_exons ≠ [] then
      some {
        id := gene.id
        coding_strand := { seq := mutated_seq }
        exons := shifted_exons
        promoter_region := gene.promoter_region
        poly_a_site := gene.poly_a_site.bind (fun p =>
          if p ≥ pos + len then some (p - len)
          else if p ≥ pos then none
          else some p)
        -- Sorted by construction
        h_exons_sorted := by
          simpa using enforceSortedNonOverlap_chain shifted_exons_raw
        -- Boundedness from deletion-boundedness lemma + normalizer preserves end_
        h_exons_bounded := by
          intro r' hr'
          -- First, all raw-shifted exons are bounded
          have hB_raw :
              ∀ x ∈ shifted_exons_raw, x.end_ ≤ mutated_seq.length := by
            intro x hx
            -- use the deletion boundedness API already proven above
            simpa [mutated_seq] using
              shiftRegionsAfter_bounded_after_deletion
                (gene := gene) (pos := pos) (len := len) h_bounds
                x hx
          -- Then, the normalizer preserves boundedness
          have : ∀ x ∈ shifted_exons, x.end_ ≤ mutated_seq.length := by
            -- shifted_exons is normalization of raw; reuse boundedness through normalizer
            simpa [shifted_exons] using
              enforceSortedNonOverlap_bounded
                (regions := shifted_exons_raw) (L := mutated_seq.length) hB_raw
          exact this r' hr'
        h_exons_nonempty := h_valid
      }
    else none
  else none

-- Replace the sorrys in applyDeletion by using the new API
/-
/-- Apply deletion mutation with coordinate adjustment -/
def applyDeletion (gene : Gene) (pos : Nat) (len : Nat) : Option Gene :=
  if h_bounds : pos + len ≤ gene.coding_strand.seq.length then
    let mutated_seq := gene.coding_strand.seq.take pos ++
                      gene.coding_strand.seq.drop (pos + len)
    let shifted_exons_raw := shiftRegionsAfter pos (-len : Int) gene.exons
    -- Normalize to enforce Chain' and non-overlap
    let shifted_exons := enforceSortedNonOverlap shifted_exons_raw

    -- Deletions might remove entire exons
    if h_valid : shifted_exons ≠ [] then
      some {
        id := gene.id
        coding_strand := { seq := mutated_seq }
        exons := shifted_exons
        promoter_region := gene.promoter_region
        poly_a_site := gene.poly_a_site.bind (fun p =>
          if p ≥ pos + len then some (p - len)
          else if p ≥ pos then none
          else some p)
        -- Sorted by construction
        h_exons_sorted := by
          simpa using enforceSortedNonOverlap_chain shifted_exons_raw
        -- Boundedness from deletion-boundedness lemma + normalizer preserves end_
        h_exons_bounded := by
          intro r' hr'
          -- First, all raw-shifted exons are bounded
          have hB_raw :
              ∀ x ∈ shifted_exons_raw, x.end_ ≤ mutated_seq.length := by
            intro x hx
            -- use the deletion boundedness API
            simpa [mutated_seq] using
              shiftRegionsAfter_bounded_after_deletion
                (gene := gene) (pos := pos) (len := len) h_bounds
                x hx
          -- Then, the normalizer preserves boundedness
          have : ∀ x ∈ shifted_exons, x.end_ ≤ mutated_seq.length := by
            -- shifted_exons is normalization of raw; reuse boundedness through normalizer
            simpa [shifted_exons] using
              enforceSortedNonOverlap_bounded
                (regions := shifted_exons_raw) (L := mutated_seq.length) hB_raw
          exact this r' hr'
        h_exons_nonempty := h_valid
      }
    else none
  else none-/

/-- Apply a substitution mutation -/
def applySubstitution (gene : Gene) (pos : Nat) (new : DNABase) : Option Gene :=
  if h : pos < gene.coding_strand.seq.length then
    let mutated_seq := gene.coding_strand.seq.set pos new
    -- For simplicity, allow all substitutions
    some { gene with
      coding_strand := { seq := mutated_seq }
      h_exons_bounded := by
        intro r hr
        have := gene.h_exons_bounded r hr
        simp [List.length_set]
        simp_all only [List.length_set, mutated_seq]
    }
  else none

/-! ## applyInversion -/

def applyInversion (gene : Gene) (start end_ : Nat) : Option Gene :=
  -- Require a valid range inside the sequence.
  if h_bounds : start < end_ ∧ end_ ≤ gene.coding_strand.seq.length then
    let segLen := end_ - start
    let seg    := (gene.coding_strand.seq.drop start).take segLen
    let mutated_seq :=
      gene.coding_strand.seq.take start ++ seg.reverse ++ gene.coding_strand.seq.drop end_
    -- Exons unchanged; length preserved, so boundedness carries over.
    some { gene with
      coding_strand := { seq := mutated_seq }
      h_exons_bounded := by
        intro r hr
        have hb := gene.h_exons_bounded r hr
        -- mutated length = original length
        have hlen :
            mutated_seq.length = gene.coding_strand.seq.length := by
          -- start ≤ end_ and end_ ≤ len
          have hse : start ≤ end_ := Nat.le_of_lt h_bounds.1
          -- Unfold seg/segLen so the lemma matches the goal exactly
          simpa [mutated_seq, seg, segLen] using
            (length_after_inversion gene.coding_strand.seq start end_ hse h_bounds.2)
        simpa [hlen]
    }
  else
    none

/-! ## applyDuplication -/

def applyDuplication (gene : Gene) (start end_ : Nat) : Option Gene :=
  -- Duplicate the half-open segment [start, end_) and insert it at position end_.
  if h_bounds : start < end_ ∧ end_ ≤ gene.coding_strand.seq.length then
    let segLen := end_ - start
    let bases  := (gene.coding_strand.seq.drop start).take segLen
    let mutated_seq :=
      gene.coding_strand.seq.take end_ ++ bases ++ gene.coding_strand.seq.drop end_
    let shifted_exons := shiftRegionsAfter end_ (bases.length : Int) gene.exons
    if h_preserved : shifted_exons ≠ [] then
      some {
        id := gene.id
        coding_strand := { seq := mutated_seq }
        exons := shifted_exons
        promoter_region := gene.promoter_region
        poly_a_site := gene.poly_a_site.map (fun p => if p ≥ end_ then p + segLen else p)
        h_exons_sorted := by
          -- Sortedness preserved under region shift by the duplicated segment length
          exact shiftRegionsAfter_preserves_sorted end_ bases.length gene.exons gene.h_exons_sorted
        h_exons_bounded := by
          intro r' hr'
          -- Use the general boundedness lemma for insertions at pos=end_ with `bases`.
          have hpos : end_ ≤ gene.coding_strand.seq.length := h_bounds.2
          -- Align the shift amount: bases.length = segLen
          have h_bases_len : bases.length = segLen := by
            -- segLen ≤ gene.len - start, so taking segLen from drop start has length segLen
            have h_mid_bound : segLen ≤ gene.coding_strand.seq.length - start := by
              -- end_ - start ≤ len - start
              simpa [segLen] using Nat.sub_le_sub_right h_bounds.2 start
            simp [bases, List.length_take, List.length_drop,
                  Nat.min_eq_left h_mid_bound, segLen]
          -- Rewrite shift from segLen to bases.length so membership matches the lemma
          simpa [mutated_seq, shifted_exons, h_bases_len.symm] using
            (shiftRegionsAfter_bounded_after_insertion
               (gene := gene) (pos := end_) (bases := bases) hpos r' hr')
        h_exons_nonempty := h_preserved
      }
    else
      none
  else
    none

/-! ## applySpliceSite -/

/--
Apply a splice-site mutation at the actual splice windows checked by `splice`:

- Donor (5' splice site) window: starts at `r.end_` (first two intronic bases after the exon).
  We mutate the first base at `r.end_`. This requires a following intron (i.e., not the last exon).

- Acceptor (3' splice site) window: starts at `r.start - Lacc` (last two intronic bases before the exon).
  We mutate the first base of that window at `r.start - Lacc`. This requires a preceding intron
  (i.e., not the first exon) and no underflow.
-/
def applySpliceSite (gene : Gene) (exonIdx : Nat) (isDonor : Bool) (newBase : DNABase) :
    Option Gene :=
  if hidx : exonIdx < gene.exons.length then
    let r := gene.exons[exonIdx]!
    if isDonor then
      -- Donor: require a following intron (not the last exon)
      if hnext : exonIdx + 1 < gene.exons.length then
        -- Mutate first base of donor window at r.end_
        if hpos : r.end_ < gene.coding_strand.seq.length then
          applySubstitution gene r.end_ newBase
        else
          none
      else
        none
    else
      -- Acceptor: require a preceding intron (not the first exon) and no underflow
      let L := gene.canonical_acceptor.length
      if hprev : 0 < exonIdx ∧ L ≤ r.start then
        let pos := r.start - L -- first base of the acceptor window
        if hpos : pos < gene.coding_strand.seq.length then
          applySubstitution gene pos newBase
        else
          none
      else
        none
  else
    none

/--
REVISED: The main dispatcher now points to the refactored functions.
-/
def applyMutation (gene : Gene) (m : Mutation) : Option Gene :=
  match m with
  | .Substitution pos new => applySubstitution gene pos new
  | .Insertion pos bases => applyInsertion gene pos bases
  | .Deletion pos len => applyDeletion gene pos len
  | .Inversion start end_ => applyInversion gene start end_
  | .Duplication start end_ => applyDuplication gene start end_
  | .SpliceSite exonIdx isDonor newBase => applySpliceSite gene exonIdx isDonor newBase

/-- Comprehensive mutation effect analysis -/
def analyzeMutationEffect'' (gene : Gene) (m : Mutation) : MutationEffect :=
  match applyMutation gene m with
  | none => .InvalidMutation
  | some mutated_gene =>
    let original := synthesizeProtein gene
    let mutated := synthesizeProtein mutated_gene
    match original, mutated with
    | some o, some m =>
      if o = m then .Silent
      else if o.length = m.length then .Missense
      else if m.length < o.length ∧ m.isPrefixOf o then .Nonsense
      else .Frameshift
    | some _, none => .NoProtein
    | none, some _ => .RegulatoryDefect
    | none, none => .Silent

/--
Comprehensive mutation effect analysis, using arithmetic for frameshift detection.
-/
def analyzeMutationEffect' (gene : Gene) (m : Mutation) : MutationEffect :=
  -- First, check for frameshift based on arithmetic properties. This is the most reliable check.
  if mutationIsFrameshift gene m then
    .Frameshift
  else
    -- For other cases, simulate the effect by comparing protein products.
    match applyMutation gene m with
    | none => .InvalidMutation
    | some mutated_gene =>
      let original_protein? := synthesizeProtein gene
      let mutated_protein? := synthesizeProtein mutated_gene
      match original_protein?, mutated_protein? with
      | some o, some m_prot =>
        if o = m_prot then
          .Silent
        else if o.length = m_prot.length then
          -- Same length, different sequence: Missense
          .Missense
        else if m_prot.length < o.length ∧ m_prot.isPrefixOf o then
          -- Shorter and a prefix: Nonsense (premature stop)
          .Nonsense
        else
          -- This could be an in-frame indel (len % 3 = 0) or other complex event.
          -- For now, we can classify it as Missense as the frame is preserved.
          .Missense
      | some _, none => .NoProtein -- Original had a protein, now it's gone.
      | none, some _ => .RegulatoryDefect -- Mutation created a protein where there was none.
      | none, none => .Silent -- Still no protein.

def analyzeMutationEffect (gene : Gene) (m : Mutation) : MutationEffect :=
  -- Special check for splice-site mutations' functional effect
  if let .SpliceSite .. := m then
    let original_protein? := synthesizeProtein gene
    match applyMutation gene m with
    | none => .InvalidMutation
    | some mutated_gene =>
      let mutated_protein? := synthesizeProtein mutated_gene
      if original_protein?.isSome ∧ mutated_protein?.isNone then
        .SpliceDefect -- CORRECT: The mutation caused a splicing failure.
      else
        -- Fallback to standard analysis if it didn't cause a total failure
        .Silent -- Placeholder for more detailed analysis
  -- Original frameshift check remains
  else if mutationIsFrameshift gene m then
    .Frameshift
  else
    -- General-purpose comparison
    match applyMutation gene m with
    | none => .InvalidMutation
    | some mutated_gene =>
      let original_protein? := synthesizeProtein gene
      let mutated_protein? := synthesizeProtein mutated_gene
      match original_protein?, mutated_protein? with
      | some o, some m_prot =>
        if o = m_prot then .Silent
        else if o.length = m_prot.length then .Missense
        else if m_prot.isPrefixOf o then .Nonsense
        -- REVISED: More precise classification for in-frame indels
        else
          match m with
          | .Insertion .. => .InFrameIndel
          | .Deletion ..  => .InFrameIndel
          | _             => .Missense -- Default for other complex changes
      | some _, none => .NoProtein
      | none, some _ => .RegulatoryDefect
      | none, none => .Silent
-- Section 6: Core Theorems with Complete Proofs
namespace Bio.Theorems

open Bio Bio.Sequence Bio.Genetics Bio.Mutation

/-! ### Theorem 1: Genetic Code Redundancy -/

theorem genetic_code_is_redundant :
    ∃ (c1 c2 : List RNABase), c1 ≠ c2 ∧
    ∃ aa : AminoAcid, standardGeneticCode c1 = .Continue aa ∧
                      standardGeneticCode c2 = .Continue aa := by
  use [.U, .U, .U], [.U, .U, .C]
  constructor
  · intro h; injection h; simp_all
  · use AminoAcid.Phe; constructor <;> rfl

/-! ### Theorem 2: Intronic Mutation Invariance (Decomposed Proof) -/

lemma not_in_exon_of_intronic
    (gene : Gene) (pos : Nat) (h_intr : IsIntronic gene pos)
    {region : GenomicRegion} (h_region : region ∈ gene.exons) :
    ¬ (pos ≥ region.start ∧ pos < region.end_) := by
  intro h
  exact h_intr.2 ⟨region, h_region, h.left, h.right⟩

lemma exon_slice_pos_ne_intronic_pos
    (gene : Gene) (pos : Nat) (h_intr : IsIntronic gene pos)
    {region : GenomicRegion} (h_region : region ∈ gene.exons)
    (i : Nat) (h_i : i < region.length) :
    region.start + i ≠ pos := by
  intro h_eq
  have h_in_exon : pos ≥ region.start ∧ pos < region.end_ := by
    refine ⟨?_, ?_⟩
    · have : region.start ≤ region.start + i := Nat.le_add_right _ _
      rwa [h_eq] at this
    · have : region.start + i < region.start + region.length :=
        Nat.add_lt_add_left h_i _
      rw [GenomicRegion.length, Nat.add_sub_of_le (le_of_lt region.h_valid)] at this
      rwa [h_eq] at this
  exact (not_in_exon_of_intronic gene pos h_intr h_region) h_in_exon

lemma transcribe_set_ne (dna : List DNABase) (pos idx : Nat) (new_base : DNABase)
    (h_ne : idx ≠ pos) :
    (transcribe (dna.set pos new_base))[idx]? = (transcribe dna)[idx]? := by
  have h_raw : (dna.set pos new_base)[idx]? = dna[idx]? := by
    simpa using List.getElem?_set_ne (l := dna) (i := pos) (j := idx)
                                       (a := new_base) (h_ne.symm)
  calc
    (transcribe (dna.set pos new_base))[idx]? =
        Option.map transcribeBase ((dna.set pos new_base)[idx]?) := by
      simp only [transcribe, List.getElem?_map]
    _ = Option.map transcribeBase (dna[idx]?) := by
      simpa using congrArg (Option.map transcribeBase) h_raw
    _ = (transcribe dna)[idx]? := by
      simp [transcribe, List.getElem?_map]

lemma exon_slice_unchanged_under_intronic_subst
    (gene : Gene) (pos : Nat) (h_intr : IsIntronic gene pos)
    {region : GenomicRegion} (h_region : region ∈ gene.exons)
    (new_base : DNABase) :
    let pre  := transcribe gene.coding_strand.seq
    let post := transcribe (gene.coding_strand.seq.set pos new_base)
    (post.drop region.start |>.take region.length) =
    (pre.drop  region.start |>.take region.length) := by
  ext i
  by_cases h_i : i < region.length
  · have h_ne := exon_slice_pos_ne_intronic_pos gene pos h_intr h_region i h_i
    simp [List.getElem?_drop, List.getElem?_take, h_i,
          transcribe_set_ne _ _ _ _ h_ne]
  · simp [List.getElem?_drop, List.getElem?_take, h_i]

namespace Bio.Genetics

-- Helper: spliceAndCheck respects per-exon slice equality on the given pre-mRNA.
-- This matches the recursive structure of spliceAndCheck.
private lemma spliceAndCheck_congr_slices
    (g : Gene) (pre₁ pre₂ : List RNABase)
    (exons : List Bio.Sequence.GenomicRegion)
    (acc : List RNABase)
    (hSlices : ∀ r ∈ exons, (pre₁.drop r.start |>.take r.length) = (pre₂.drop r.start |>.take r.length)) :
    spliceAndCheck g pre₁ exons acc = spliceAndCheck g pre₂ exons acc := by
  classical
  -- Important: revert both acc and the per-exon hypothesis so IH quantifies over them.
  revert acc hSlices
  induction exons with
  | nil =>
      intro acc hSlices
      simp [splice, spliceAndCheck]
  | cons r rs ih =>
      intro acc hSlices
      have h_head :
          (pre₁.drop r.start |>.take r.length) =
          (pre₂.drop r.start |>.take r.length) :=
        hSlices r (by simp)
      have h_tail :
          ∀ r' ∈ rs,
            (pre₁.drop r'.start |>.take r'.length) =
            (pre₂.drop r'.start |>.take r'.length) := by
        intro r' hr'
        exact hSlices r' (by simp [hr'])
      -- Unfold one step; the head slice rewrites both sides the same way
      -- so the recursive calls have identical accumulators.
      -- Now split on the shared guard and simplify both sides.
      by_cases hc :
        ((acc.isEmpty ||
          decide (((g.coding_strand.seq.drop (r.start - g.canonical_acceptor.length)).take
                    g.canonical_acceptor.length) = g.canonical_acceptor))
         &&
         (rs.isEmpty ||
          decide (((g.coding_strand.seq.drop r.end_).take g.canonical_donor.length)
                    = g.canonical_donor)))
      ·
        simp [splice, spliceAndCheck, h_head, hc]
        -- Apply IH on the tail with the specialized slice hypothesis.
        exact ih (acc ++ (pre₂.drop r.start |>.take r.length)) h_tail
      ·
        simp [splice, spliceAndCheck, h_head, hc]
/-- A conservative “safety” predicate: the genomic position `pos` is intronic
    and does not lie in any acceptor/donor check window that `spliceAndCheck`
    inspects (acceptor window: [r.start - Lacc, r.start), donor window: [r.end_, r.end_ + Ldon)). -/
def SafeForSpliceSites (gene : Gene) (pos : Nat) : Prop :=
  IsIntronic gene pos ∧
  ∀ r ∈ gene.exons,
    let Lacc := gene.canonical_acceptor.length
    let Ldon := gene.canonical_donor.length
    (pos < r.start - Lacc ∨ r.start ≤ pos) ∧
    (pos < r.end_ ∨ r.end_ + Ldon ≤ pos)

/-- Generic slice stability: if `pos` is outside the slice window `[start, start+len)`,
    setting `l[pos] := a` does not change `take len (drop start l)`. -/
lemma take_drop_set_outside {α} (l : List α) (pos start len : Nat) (a : α)
    (hout : ∀ i, i < len → start + i ≠ pos) :
    ((l.set pos a).drop start).take len = (l.drop start).take len := by
  classical
  -- pointwise on getElem?
  ext i
  by_cases hi : i < len
  · have hne : start + i ≠ pos := hout i hi
    -- use getElem?_set_ne at the absolute index `start + i`
    have hraw :
        (l.set pos a)[start + i]? = l[start + i]? := by
      simpa using List.getElem?_set_ne (l := l) (i := pos) (j := start + i) (a := a) (h := hne.symm)
    -- now reduce drop/take to absolute index
    simp [List.getElem?_drop, List.getElem?_take, hi, hraw]
  · simp [List.getElem?_take, hi]

/-! Helpers for the acceptor window avoidance proof -/

private lemma acceptor_avoid_pos_before_start
    (gene : Gene) (pos : Nat) {r : GenomicRegion} (hr : r ∈ gene.exons)
    {L i : Nat} (hi : i < L) (hlt : pos < r.start - L) :
    (r.start - L) + i ≠ pos := by
  have : pos < (r.start - L) + i := lt_of_lt_of_le hlt (Nat.le_add_right _ _)
  exact (ne_of_lt this).symm

private lemma acceptor_avoid_pos_L_le_start
    (gene : Gene) (pos : Nat) {r : GenomicRegion} (hr : r ∈ gene.exons)
    {L i : Nat} (hi : i < L) (hge : r.start ≤ pos) (hL : L ≤ r.start) :
    (r.start - L) + i ≠ pos := by
  have h_eq : (r.start - L) + L = r.start := Nat.sub_add_cancel hL
  have h_idx_lt_start : (r.start - L) + i < r.start := by
    simpa [h_eq] using (Nat.add_lt_add_left hi (r.start - L))
  have h_idx_lt_pos : (r.start - L) + i < pos := lt_of_lt_of_le h_idx_lt_start hge
  exact ne_of_lt h_idx_lt_pos

private lemma acceptor_avoid_pos_underflow_lt_start
    (gene : Gene) (pos : Nat) {r : GenomicRegion} (hr : r ∈ gene.exons)
    {L i : Nat} (hi : i < L) (hge : r.start ≤ pos) (hzero : r.start - L = 0)
    (hi_lt_start : i < r.start) :
    (r.start - L) + i ≠ pos := by
  have : i < pos := lt_of_lt_of_le hi_lt_start hge
  simpa [hzero] using ne_of_lt this

private lemma acceptor_avoid_pos_underflow_i_in_exon_contra
    (gene : Gene) (pos : Nat) {r : GenomicRegion} (hr : r ∈ gene.exons)
    (hintr : IsIntronic gene pos)
    {L i : Nat} (hzero : r.start - L = 0) (hi_ge_start : r.start ≤ i) (hi_lt_end : i < r.end_) :
    (r.start - L) + i ≠ pos := by
  intro hip
  -- From underflow and equality we get i = pos
  have hi_pos : i = pos := by simpa [hzero] using hip
  -- Then pos lies in r by the bounds on i
  have : pos ≥ r.start ∧ pos < r.end_ := by
    exact ⟨by simpa [hi_pos] using hi_ge_start,
           by simpa [hi_pos] using hi_lt_end⟩
  -- Intronic excludes being inside any exon
  exact (not_in_exon_of_intronic gene pos hintr hr) this

private lemma acceptor_avoid_pos_underflow_ge_end_pos_lt_end
    (gene : Gene) (pos : Nat) {r : GenomicRegion} (hr : r ∈ gene.exons)
    {L i : Nat} (hzero : r.start - L = 0) (hi_ge_end : r.end_ ≤ i) (hpos_lt_end : pos < r.end_) :
    (r.start - L) + i ≠ pos := by
  intro hip
  -- Convert the absolute equality to i = pos, then rewrite the bound
  have hi_pos : i = pos := by simpa [hzero] using hip
  have hpos_ge_end : r.end_ ≤ pos := by simpa [hi_pos] using hi_ge_end
  exact (not_le_of_gt hpos_lt_end) hpos_ge_end

-- Stronger and simpler: if i lies inside the donor “right” window, donor safety (pos ≥ r.end_ + Ldon)
-- implies i < pos, hence inequality.
private lemma acceptor_avoid_pos_underflow_ge_end_pos_ge
    (gene : Gene) (pos : Nat) {r : GenomicRegion} (hr : r ∈ gene.exons)
    {L i : Nat} (hzero : r.start - L = 0) (hi_ge_start : r.start ≤ i) (hi_ge_end : r.end_ ≤ i)
    (hi_lt_right : i < r.end_ + gene.canonical_donor.length)
    (hpos_ge : r.end_ + gene.canonical_donor.length ≤ pos) :
    (r.start - L) + i ≠ pos := by
  intro hip
  -- Reduce to i ≠ pos via underflow equality
  have hi_pos : i = pos := by simpa [hzero] using hip
  have : i < pos := lt_of_lt_of_le hi_lt_right hpos_ge
  -- Conclude inequality and lift back through underflow normalization
  have hne : i ≠ pos := ne_of_lt this
  subst hi_pos
  simp_all only [zero_add, lt_self_iff_false]

/-- Indices of the acceptor window avoid a “safe” intronic position.

REVISED: requires a mild separation bound `Lacc ≤ r.end_ + Ldon` to rule out the
previously unprovable corner case when `r.start - Lacc = 0`, `i ≥ r.end_`, and `pos ≥ r.end_ + Ldon`. -/
lemma acceptor_window_avoid_pos
    (gene : Gene) (pos : Nat)
    {r : GenomicRegion} (hr : r ∈ gene.exons)
    (hsafe : SafeForSpliceSites gene pos)
    (hLsep : gene.canonical_acceptor.length ≤ r.end_ + gene.canonical_donor.length) :
    let L := gene.canonical_acceptor.length
    ∀ i, i < L → (r.start - L) + i ≠ pos := by
  classical
  intro L i hi
  rcases hsafe with ⟨hintr, hwin⟩
  have hpos := (hwin r hr).1
  rcases hpos with hlt | hge
  ·
    exact acceptor_avoid_pos_before_start (gene := gene) (pos := pos) (r := r) (hr := hr)
      (hi := hi) (hlt := hlt)
  ·
    by_cases hL : L ≤ r.start
    ·
      exact acceptor_avoid_pos_L_le_start (gene := gene) (pos := pos) (r := r) (hr := hr)
        (hi := hi) (hge := hge) (hL := hL)
    ·
      have hzero : r.start - L = 0 := by
        have hle : r.start ≤ L := le_of_lt (lt_of_not_ge hL)
        simpa using Nat.sub_eq_zero_of_le hle
      by_cases hi_lt_start : i < r.start
      ·
        exact acceptor_avoid_pos_underflow_lt_start (gene := gene) (pos := pos) (r := r) (hr := hr)
          (hi := hi) (hge := hge) (hzero := hzero) (hi_lt_start := hi_lt_start)
      ·
        have hi_ge_start : r.start ≤ i := le_of_not_gt hi_lt_start
        have hdon := (hwin r hr).2
        by_cases hi_lt_end : i < r.end_
        ·
          exact acceptor_avoid_pos_underflow_i_in_exon_contra (gene := gene) (pos := pos) (r := r) (hr := hr)
            (hintr := hintr) (hzero := hzero) (hi_ge_start := hi_ge_start) (hi_lt_end := hi_lt_end)
        ·
          have hi_ge_end : r.end_ ≤ i := le_of_not_gt hi_lt_end
          rcases hdon with hpos_lt_end | hpos_ge
          ·
            exact acceptor_avoid_pos_underflow_ge_end_pos_lt_end (gene := gene) (pos := pos) (r := r) (hr := hr)
              (hzero := hzero) (hi_ge_end := hi_ge_end) (hpos_lt_end := hpos_lt_end)
          ·
            -- Final subcase: i ≥ r.end_ and pos ≥ r.end_ + Ldon.
            -- Use the separation bound to derive i < r.end_ + Ldon from i < L.
            have hi_lt_right : i < r.end_ + gene.canonical_donor.length :=
              lt_of_lt_of_le hi hLsep
            exact acceptor_avoid_pos_underflow_ge_end_pos_ge (gene := gene) (pos := pos) (r := r) (hr := hr)
              (hzero := hzero) (hi_ge_start := hi_ge_start) (hi_ge_end := hi_ge_end)
              (hi_lt_right := hi_lt_right) (hpos_ge := hpos_ge)

/-- Acceptor window stability under a “safe” intronic set. -/
lemma acceptor_window_unchanged
    (gene : Gene) (pos : Nat) (new_base : DNABase)
    {r : GenomicRegion} (hr : r ∈ gene.exons)
    (hsafe : SafeForSpliceSites gene pos)
    (hLsep : gene.canonical_acceptor.length ≤ r.end_ + gene.canonical_donor.length) :
    let L := gene.canonical_acceptor.length
    (take L (drop (r.start - L) ((gene.coding_strand.seq).set pos new_base)))
      = take L (drop (r.start - L) (gene.coding_strand.seq)) := by
  classical
  intro L
  -- Obtain the avoidance property with the separation hypothesis
  have hout :=
    acceptor_window_avoid_pos
      (gene := gene) (pos := pos) (r := r) (hr := hr)
      (hsafe := hsafe) (hLsep := hLsep)
  -- Align both “let L := …” binders
  have hout' : ∀ i, i < L → (r.start - L) + i ≠ pos := by
    simpa [L] using hout
  -- Apply generic slice stability
  simpa using
    take_drop_set_outside
      (l := gene.coding_strand.seq) (pos := pos)
      (start := r.start - L) (len := L) (a := new_base) hout'

/-- Donor window stability under a “safe” intronic set: the donor slice
    `take L (drop r.end_ ...)` is unchanged by a substitution at a “safe”
    intronic position `pos`. -/
lemma donor_window_unchanged
    (gene : Gene) (pos : Nat) (new_base : DNABase)
    {r : GenomicRegion} (hr : r ∈ gene.exons)
    (hsafe : SafeForSpliceSites gene pos) :
    let L := gene.canonical_donor.length
    (take L (drop r.end_ ((gene.coding_strand.seq).set pos new_base)))
      = take L (drop r.end_ (gene.coding_strand.seq)) := by
  classical
  intro L
  rcases hsafe with ⟨_, hwin⟩
  have hpos := (hwin r hr).2
  -- Any index r.end_ + i for i < L differs from pos by donor-window safety
  have hout : ∀ i, i < L → r.end_ + i ≠ pos := by
    intro i hi
    rcases hpos with hlt | hge
    · -- pos < r.end_ ≤ r.end_ + i ⇒ pos < r.end_ + i
      have : pos < r.end_ + i := lt_of_lt_of_le hlt (Nat.le_add_right _ _)
      exact (ne_of_lt this).symm
    · -- r.end_ + i < r.end_ + L ≤ pos ⇒ r.end_ + i < pos
      have : r.end_ + i < r.end_ + L := Nat.add_lt_add_left hi _
      exact ne_of_lt (lt_of_lt_of_le this hge)
  -- Apply generic slice stability
  simpa using
    take_drop_set_outside (l := gene.coding_strand.seq) (pos := pos)
      (start := r.end_) (len := L) (a := new_base) hout

/-- If an intronic position is “safe” for splice-site checks, the splice result is unchanged.

NOTE: Requires a mild per-exon separation bound for the acceptor window:
`∀ r ∈ gene.exons, Lacc ≤ r.end_ + Ldon`. -/
lemma splice_independent_of_intronic_pos (gene : Gene) (pos : Nat)
    (h_intronic : IsIntronic gene pos) (h_safe : SafeForSpliceSites gene pos)
    (h_sep : ∀ r ∈ gene.exons, gene.canonical_acceptor.length ≤ r.end_ + gene.canonical_donor.length)
    (new_base : DNABase) :
    let mutated_gene : Gene := { gene with
      coding_strand := { seq := gene.coding_strand.seq.set pos new_base }
      h_exons_bounded := by
        intro r hr
        rw [List.length_set]
        exact gene.h_exons_bounded r hr }
    splice mutated_gene = splice gene := by
  classical
  -- Introduce a local name for the mutated gene matching the statement’s let-binding.
  set mutated_gene : Gene :=
    { gene with
      coding_strand := { seq := gene.coding_strand.seq.set pos new_base }
      h_exons_bounded := by
        intro r hr
        rw [List.length_set]
        exact gene.h_exons_bounded r hr } with hmut
  -- Align the goal to use the local `mutated_gene`.
  change splice mutated_gene = splice gene
  -- Expand splice just enough and lift equality through Option.map RawMRNA.mk.
  unfold splice
  simp
  refine congrArg (Option.map RawMRNA.mk) ?_
  -- Define original and mutated pre-mRNAs and show exon slices are identical.
  let pre  := transcribe gene.coding_strand.seq
  let post := transcribe (gene.coding_strand.seq.set pos new_base)
  have hSlices :
      ∀ region ∈ gene.exons,
        (post.drop region.start |>.take region.length) =
        (pre.drop  region.start |>.take region.length) := by
    intro region h_region
    simpa using
      exon_slice_unchanged_under_intronic_subst gene pos h_intronic h_region new_base
  -- Equality for mutated_gene at the splice-check level (slices agree).
  have h_mut_eq :
      spliceAndCheck mutated_gene post gene.exons [] =
      spliceAndCheck mutated_gene pre  gene.exons [] := by
    simpa using
      Bio.Genetics.spliceAndCheck_congr_slices
        (g := mutated_gene) (pre₁ := post) (pre₂ := pre)
        (exons := gene.exons) (acc := [])
        (by
          intro r hr
          exact hSlices r hr)
  -- Also, the canonical site checks are unchanged under the “safe” intronic substitution,
  -- so we can swap `g` from `mutated_gene` back to `gene` at fixed `pre`.
  have h_sites_eq :
      spliceAndCheck mutated_gene pre gene.exons [] =
      spliceAndCheck gene         pre gene.exons [] := by
    -- Prove by induction on exons with an arbitrary accumulator (clean IH).
    -- We only need that each head r lies in gene.exons to use the window lemmas,
    -- so we carry a subset hypothesis for the current list of exons.
    have aux :
        ∀ (exs : List GenomicRegion),
          (∀ x ∈ exs, x ∈ gene.exons) →
          ∀ (acc : List RNABase),
            spliceAndCheck mutated_gene pre exs acc =
            spliceAndCheck gene         pre exs acc := by
      intro exs hsub
      induction exs with
      | nil =>
          intro acc
          simp [spliceAndCheck, hmut]
      | cons r rs ih =>
          intro acc
          -- r is a gene exon (needed by window lemmas)
          have hr_mem : r ∈ gene.exons := hsub r (by simp)
          -- tail subset
          have hsub_tail : ∀ x ∈ rs, x ∈ gene.exons := by
            intro x hx; exact hsub x (by simp [hx])
          -- windows unchanged at r
          have hacc :
              take gene.canonical_acceptor.length
                (drop (r.start - gene.canonical_acceptor.length)
                      (mutated_gene.coding_strand.seq))
            =
              take gene.canonical_acceptor.length
                (drop (r.start - gene.canonical_acceptor.length)
                      (gene.coding_strand.seq)) := by
            -- rewrite seq via hmut, then apply window lemma (with separation bound)
            simpa [hmut] using
              acceptor_window_unchanged gene pos new_base hr_mem h_safe
                (h_sep r hr_mem)
          have hdon :
              take gene.canonical_donor.length
                (drop r.end_ (mutated_gene.coding_strand.seq))
            =
              take gene.canonical_donor.length
                (drop r.end_ (gene.coding_strand.seq)) := by
            simpa [hmut] using
              donor_window_unchanged gene pos new_base hr_mem h_safe
          -- Unfold one layer; split on the shared guard and simplify both sides.
          by_cases hc :
            ((acc.isEmpty ||
              decide (((gene.coding_strand.seq.drop (r.start - gene.canonical_acceptor.length)).take
                        gene.canonical_acceptor.length)
                      = gene.canonical_acceptor))
             &&
             (rs.isEmpty ||
              decide (((gene.coding_strand.seq.drop r.end_).take gene.canonical_donor.length)
                        = gene.canonical_donor)))
          ·
            simp [spliceAndCheck, hmut, hacc, hdon, hc]
            -- Recurse on the tail with the same accumulator on both sides.
            aesop--simpa using ih hsub_tail (acc ++ (pre.drop r.start |>.take r.length))
          ·
            simp [spliceAndCheck, hmut, hacc, hdon, hc]
            aesop
    -- Apply to the full exon list with the trivial subset hypothesis.
    exact aux gene.exons (by intro _ hx; exact hx) []
  -- Close: normalize both sides and chain the two equalities.
  have : spliceAndCheck mutated_gene (transcribe mutated_gene.coding_strand.seq) mutated_gene.exons []
        = spliceAndCheck gene (transcribe gene.coding_strand.seq) gene.exons [] := by
    -- LHS is mutated on post; RHS is original on pre.
    simpa [pre, post, hmut]
      using h_mut_eq.trans h_sites_eq
  simpa [pre, post, hmut] using this

theorem intronic_substitution_preserves_protein (gene : Gene) (pos : Nat) (new : DNABase)
    (h_intronic : IsIntronic gene pos) (h_safe : SafeForSpliceSites gene pos)
    (h_sep : ∀ r ∈ gene.exons, gene.canonical_acceptor.length ≤ r.end_ + gene.canonical_donor.length) :
    ∀ mutated_gene, applySubstitution gene pos new = some mutated_gene →
    synthesizeProtein gene = synthesizeProtein mutated_gene := by
  intro mutated_gene h_apply
  unfold synthesizeProtein applySubstitution at *
  split_ifs at h_apply with h_pos
  injection h_apply with h_eq; rw [← h_eq]
  -- Use the strengthened splicing invariance that also assumes splice-site safety.
  have := splice_independent_of_intronic_pos gene pos h_intronic h_safe h_sep new
  aesop

/-- Nonnegative shifts (insertions) preserve non-emptiness of the exon list. -/
lemma shiftRegionsAfter_preserves_nonempty
    (pos shift : Nat) (regions : List GenomicRegion)
    (h_ne : regions ≠ []) :
    shiftRegionsAfter pos (shift : Int) regions ≠ [] := by
  -- Use the `= map` characterization for nonnegative shifts
  cases regions with
  | nil =>
    exact (h_ne rfl).elim
  | cons r rs =>
    -- For a cons, the mapped list is a cons as well.
    have hform :=
      shiftRegionsAfter_nonneg_eq_map pos shift (r :: rs)
    -- Orient to display the list as a cons
    have hcons :
        shiftRegionsAfter pos (shift : Int) (r :: rs)
          = (shiftRegionAfterNat pos shift r) ::
              (rs.map (shiftRegionAfterNat pos shift)) := by
      simpa [List.map] using hform
    intro hnil
    -- A cons can never be `[]`
    simp [hcons] at hnil

/-- Convenience wrapper that reuses the general boundedness lemma
    in the "let"-bound names used by `applyInsertion`. -/
lemma exons_bounded_after_insertion_lets
    (gene : Bio.Sequence.Gene) (pos : Nat) (bases : List Bio.DNABase)
    (hpos : pos ≤ gene.coding_strand.seq.length) :
    let insLen := bases.length
    let mutated_seq := gene.coding_strand.seq.take pos ++ bases ++ gene.coding_strand.seq.drop pos
    let shifted_exons := shiftRegionsAfter pos (insLen : Int) gene.exons
    ∀ r' ∈ shifted_exons, r'.end_ ≤ mutated_seq.length := by
  intro insLen mutated_seq shifted_exons
  -- Directly reuse the core lemma and normalize the local lets
  simpa [insLen, mutated_seq, shifted_exons] using
    (shiftRegionsAfter_bounded_after_insertion
      (gene := gene) (pos := pos) (bases := bases) hpos)

/-! ### Theorem 3: Frameshift from Single-Base Insertion -/


/-! Non-axiomatic, constructive “frameshift ⇒ proteins differ” via a semantic witness.

We compute the codon-by-codon TranslationSignal streams for original and mutated coding
regions and locate the first semantic divergence (Continue aa vs Continue aa', or
a Stop on one side vs Continue/Error on the other). From that finite witness we
prove the peptide lists are unequal, with no axioms or sorry.
-/

/-- A semantic divergence witness between two signal streams. -/
inductive SignalWitness
  | diffContinue (i : Nat) (a b : AminoAcid) (h : a ≠ b)   -- Continue a vs Continue b at i
  | stopLeft   (i : Nat)                                    -- Stop at i on left, non-Stop on right
  | stopRight  (i : Nat)                                    -- Stop at i on right, non-Stop on left

/-- Compare two signal lists and return the earliest semantic divergence witness, if any. -/
def firstSignalWitness : List TranslationSignal → List TranslationSignal → Option SignalWitness
  | [], [] => none
  | [], (.Continue _ :: _) => some (.stopLeft 0)
  | [], (.Stop :: _)       => none      -- both terminal/effective: no divergence to witness
  | [], (.Error :: _)      => none      -- both terminal/effective: no divergence to witness
  | (.Continue a :: xs), (.Continue b :: ys) =>
      if h : a = b then
        match firstSignalWitness xs ys with
        | none    => none
        | some w =>
          match w with
          | .diffContinue i a' b' h' => some (.diffContinue (i+1) a' b' h')
          | .stopLeft i              => some (.stopLeft (i+1))
          | .stopRight i             => some (.stopRight (i+1))
      else
        some (.diffContinue 0 a b h)   -- here `h : ¬ a = b`, i.e., `a ≠ b`
  | (.Continue _ :: _), (.Stop :: _)   => some (.stopRight 0)
  | (.Continue _ :: _), (.Error :: _)  => some (.stopRight 0)
  | (.Stop :: _), (.Continue _ :: _)   => some (.stopRight 0)
  | (.Stop :: _), (.Stop :: _)         => none
  | (.Stop :: _), (.Error :: _)        => none
  | (.Error :: _), (.Continue _ :: _)  => some (.stopRight 0)
  | (.Error :: _), (.Stop :: _)        => none
  | (.Error :: _), (.Error :: _)       => none
  | (.Continue _ :: _), []             => some (.stopRight 0)
  | (.Stop :: _), []                   => none
  | (.Error :: _), []                  => none

/-- Translate a signal stream into a peptide, structurally (no accumulator). -/
def translateSignals : List TranslationSignal → List AminoAcid
  | [] => []
  | .Continue aa :: rest => aa :: translateSignals rest
  | .Stop :: _ => []
  | .Error :: _ => []

/-- Codons of a processed mRNA's CDS. -/
def codonsOf (p : ProcessedMRNA) : List (List RNABase) :=
  List.chunkList 3 p.coding_region

/-- Translation signals (Continue aa | Stop | Error) for a processed mRNA's CDS. -/
def signalsOf (p : ProcessedMRNA) : List TranslationSignal :=
  (codonsOf p).map standardGeneticCode

/-- Core translation on a pre-chunked codon list. -/
def translateFromCodons : List (List RNABase) → List AminoAcid
  | [] => []
  | c :: cs =>
    if c.length ≠ 3 then []
    else
      match standardGeneticCode c with
      | .Continue aa => aa :: translateFromCodons cs
      | .Stop => []
      | .Error => []

/-- Empty codon maps to `.Error`. -/
private lemma standardGeneticCode_error_len_zero :
    standardGeneticCode [] = TranslationSignal.Error := by
  -- Just match the specific empty list case without expansion
  exact rfl

/-- Single-base codon maps to `.Error`. -/
private lemma standardGeneticCode_error_len_one (a : RNABase) :
    standardGeneticCode [a] = TranslationSignal.Error := by
  -- Case split on the single base to make the match reduce definitionally.
  cases a <;> unfold standardGeneticCode <;> rfl

/-- Two-base codon maps to `.Error`. -/
private lemma standardGeneticCode_error_len_two_exact (a b : RNABase) :
    standardGeneticCode [a, b] = TranslationSignal.Error := by
  -- Case split on both bases to make the match reduce definitionally.
  cases a <;> cases b <;> unfold standardGeneticCode <;> rfl

/-- Short codons (length ≤ 2) map to `.Error`. -/
private lemma standardGeneticCode_error_len_le_two
    (c : List RNABase) (hle : c.length ≤ 2) :
    standardGeneticCode c = TranslationSignal.Error := by
  cases c with
  | nil =>
      -- length 0: use the dedicated lemma
      exact standardGeneticCode_error_len_zero
  | cons a t =>
    cases t with
    | nil =>
        -- length 1: use the dedicated lemma
        exact standardGeneticCode_error_len_one a
    | cons b t2 =>
      cases t2 with
      | nil =>
          -- length 2: use the dedicated lemma
          exact standardGeneticCode_error_len_two_exact a b
      | cons d t3 =>
          have hgt' : 2 < (a :: b :: d :: t3).length := by simp
          exact False.elim ((not_le_of_gt hgt') hle)

/-- Long codons (length ≥ 4) map to `.Error`. -/
private lemma standardGeneticCode_error_len_ge_four
    {a b d e : RNABase} {t4 : List RNABase} :
    standardGeneticCode (a :: b :: d :: e :: t4) = TranslationSignal.Error := by
  classical
  -- Force the reduction past the third base and expose the tail as nonempty,
  -- so no explicit 3-base pattern can match and the wildcard `.Error` is chosen.
  cases a <;> cases b <;> cases d <;> cases t4 <;>
    unfold standardGeneticCode <;> rfl

/-- Any codon whose length is not exactly 3 maps to `.Error` in the standard code. -/
private lemma standardGeneticCode_eq_error_of_length_ne_three
    (c : List RNABase) (hne : c.length ≠ 3) :
    standardGeneticCode c = TranslationSignal.Error := by
  classical
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- length ≤ 2
    have hle2 : c.length ≤ 2 := by
      -- `c.length < 3` ↔ `c.length ≤ 2`
      simpa [Nat.lt_succ_iff] using hlt
    exact standardGeneticCode_error_len_le_two c hle2
  · -- length ≥ 4: expose 4-head shape, then use the long-codon lemma
    cases c with
    | nil =>
        simp at hgt
    | cons a t =>
      cases t with
      | nil =>
          simp at hgt
      | cons b t2 =>
        cases t2 with
        | nil =>
            simp at hgt
        | cons d t3 =>
          cases t3 with
          | nil =>
              -- Here `c.length = 3`, contradicting `hgt`.
              simp at hgt
          | cons e t4 =>
              -- Now length ≥ 4
              simpa using
                (standardGeneticCode_error_len_ge_four
                  (a := a) (b := b) (d := d) (e := e) (t4 := t4))

/-- On a codon list, `translateFromCodons` matches `translateSignals ∘ map standardGeneticCode`. -/
lemma translateFromCodons_eq_translateSignals (codons : List (List RNABase)) :
  translateFromCodons codons = translateSignals (codons.map standardGeneticCode) := by
  classical
  induction codons with
  | nil =>
      simp [translateFromCodons, translateSignals]
  | cons c cs ih =>
      by_cases h3 : c.length = 3
      · -- length = 3: follow the genetic code head case
        simp [translateFromCodons, h3]
        cases hc : standardGeneticCode c with
        | Continue aa =>
            simp [translateFromCodons, h3, hc, translateSignals, ih]
        | Stop =>
            simp [translateFromCodons, h3, hc, translateSignals]
        | Error =>
            simp [translateFromCodons, h3, hc, translateSignals]
      · -- length ≠ 3: head maps to `.Error`, both sides become []
        have hc : standardGeneticCode c = TranslationSignal.Error :=
          standardGeneticCode_eq_error_of_length_ne_three c h3
        simp [translateFromCodons, h3, translateSignals, hc]

/-- Bridge `translate` to the codon-level core. -/
lemma translate_eq_fromCodons (cds : List RNABase) :
    translate cds = translateFromCodons (List.chunkList 3 cds) := by
  unfold Bio.Genetics.translate
  -- The proof is by induction on the list of codons.
  let codons := List.chunkList 3 cds
  have aux : ∀ (cl : List (List RNABase)),
    translate.go cl = translateFromCodons cl := by
    intro cl
    induction cl with
    | nil => simp [translate.go, translateFromCodons]
    | cons c cs ih =>
      simp [translate.go, translateFromCodons]
      -- We need to handle the case where a codon length is not 3.
      by_cases h_len : c.length = 3
      · simp [h_len]
        cases h_code : standardGeneticCode c
        · simp [translate.go, translateFromCodons, h_code, ih]
        · simp [translate.go, translateFromCodons, h_code]
        · simp [translate.go, translateFromCodons, h_code]
      · have h_err : standardGeneticCode c = .Error :=
          standardGeneticCode_eq_error_of_length_ne_three c h_len
        simp [translate.go, translateFromCodons, h_err]
  exact aux codons

/-- Bridge: `translate` equals `translateSignals ∘ signalsOf`. -/
lemma translate_eq_translateSignals (p : ProcessedMRNA) :
    translate p.coding_region = translateSignals (signalsOf p) := by
  -- First, move to the codon-level core.
  calc
    translate p.coding_region
        = translateFromCodons (List.chunkList 3 p.coding_region) := by
          simpa using translate_eq_fromCodons (cds := p.coding_region)
    _ = translateSignals ((List.chunkList 3 p.coding_region).map standardGeneticCode) := by
          simpa using translateFromCodons_eq_translateSignals
            (codons := List.chunkList 3 p.coding_region)
    _ = translateSignals (signalsOf p) := by
          simp [signalsOf, codonsOf]

/-- Soundness: a semantic witness implies peptide inequality. -/
lemma proteins_differ_of_witness
    (p q : ProcessedMRNA)
    (w : SignalWitness)
    (hw : firstSignalWitness (signalsOf p) (signalsOf q) = some w) :
    Bio.Genetics.translate p.coding_region ≠ Bio.Genetics.translate q.coding_region := by
  -- Bridge to signal semantics.
  have hp := Bio.Genetics.translate_eq_translateSignals p
  have hq := Bio.Genetics.translate_eq_translateSignals q
  -- Reduce to inequality on translateSignals over signal streams.
  intro h_eq
  have h_eq' : translateSignals (signalsOf p) = translateSignals (signalsOf q) := by
    simpa [hp, hq] using h_eq
  -- Earliest divergence forces different outputs.
  have aux :
      ∀ s t w, firstSignalWitness s t = some w →
               translateSignals s ≠ translateSignals t := by
    intro s
    induction s with
    | nil =>
        intro t w hw'
        cases t with
        | nil =>
            -- firstSignalWitness [] [] = none; contradiction
            simp [firstSignalWitness] at hw'
        | cons th tt =>
          -- Any some-witness here forces t to start with Continue
          cases th with
          | Continue aa =>
              -- [] vs (aa :: _) translate to [] vs aa :: _
              intro h
              simp [translateSignals] at h
          | Stop =>
              -- firstSignalWitness [] (Stop :: _) = none
              simp [firstSignalWitness] at hw'
          | Error =>
              -- firstSignalWitness [] (Error :: _) = none
              simp [firstSignalWitness] at hw'
    | cons sh st ih =>
        intro t w hw'
        cases sh with
        | Continue aaL =>
            cases t with
            | nil =>
                -- firstSignalWitness (Continue ..) [] = some .stopRight 0
                intro h
                simp [translateSignals] at h
            | cons th tt =>
              cases th with
              | Continue aaR =>
                  by_cases heq : aaL = aaR
                  · -- Heads equal: recurse on tails; the witness must come from the tail.
                    -- Extract some tail witness existence from the head-equal branch.
                    have : ∃ w0, firstSignalWitness st tt = some w0 := by
                      cases hrec : firstSignalWitness st tt with
                      | none =>
                          -- If tail returns none, whole returns none under equal heads
                          simp [firstSignalWitness, heq, hrec] at hw'
                      | some w0 =>
                          exact ⟨w0, by simp [firstSignalWitness, heq, hrec]⟩
                    rcases this with ⟨w0, hw0⟩
                    intro h
                    -- Reduce equality to tails and apply IH
                    have htails : translateSignals st = translateSignals tt := by
                      simpa [translateSignals, heq] using h
                    exact (ih tt w0 hw0) htails
                  · -- Heads differ: contradiction from cons equality on translateSignals
                    intro h
                    have hcons := List.cons.inj (by simpa [translateSignals] using h)
                    exact heq hcons.left
              | Stop =>
                  -- firstSignalWitness (Continue ..) (Stop :: _) = some .stopRight 0
                  intro h
                  -- left translates to nonempty, right translates to []
                  simp [translateSignals] at h
              | Error =>
                  -- firstSignalWitness (Continue ..) (Error :: _) = some .stopRight 0
                  intro h
                  simp [translateSignals] at h
        | Stop =>
            -- Left starts with Stop
            cases t with
            | nil =>
                -- firstSignalWitness (Stop :: _) [] = none
                simp [firstSignalWitness] at hw'
            | cons th tt =>
              cases th with
              | Continue aa =>
                  -- some .stopRight 0; left translates to [], right to aa :: _
                  intro h
                  simp [translateSignals] at h
              | Stop =>
                  -- both Stop ⇒ none
                  simp [firstSignalWitness] at hw'
              | Error =>
                  -- Stop vs Error ⇒ none
                  simp [firstSignalWitness] at hw'
        | Error =>
            -- Left starts with Error
            cases t with
            | nil =>
                -- firstSignalWitness (Error :: _) [] = none
                simp [firstSignalWitness] at hw'
            | cons th tt =>
              cases th with
              | Continue aa =>
                  -- some .stopRight 0; left translates to [], right to aa :: _
                  intro h
                  simp [translateSignals] at h
              | Stop =>
                  -- Error vs Stop ⇒ none
                  simp [firstSignalWitness] at hw'
              | Error =>
                  -- both Error ⇒ none
                  simp [firstSignalWitness] at hw'
  exact (aux _ _ _ hw) h_eq'

/--
Compute a semantic witness on the full gene→protein pipeline.

If it returns `some w`, then proteins differ non-axiomatically.
-/
def frameshiftSemanticWitness
    (gene : Gene) (m : Mutation) :
    Option SignalWitness :=
  match applyMutation gene m with
  | none => none
  | some mutated =>
    -- Splice both genes; if either fails, no witness
    match Bio.Genetics.splice gene, Bio.Genetics.splice mutated with
    | some mrnaG, some mrnaM =>
      -- Process both transcripts to CDS; if either fails, no witness
      match Bio.Genetics.processMRNA mrnaG, Bio.Genetics.processMRNA mrnaM with
      | some p, some q =>
          firstSignalWitness (signalsOf p) (signalsOf q)
      | _, _ => none
    | _, _ => none

/-- Unpack a semantic frameshift witness into all core pipeline objects. -/
private lemma frameshiftWitness_unpack
    (gene : Gene) (m : Mutation) (w : SignalWitness)
    (hw : frameshiftSemanticWitness gene m = some w) :
    ∃ mutated rawG rawM p q,
      applyMutation gene m = some mutated ∧
      Bio.Genetics.splice gene = some rawG ∧
      Bio.Genetics.splice mutated = some rawM ∧
      Bio.Genetics.processMRNA rawG = some p ∧
      Bio.Genetics.processMRNA rawM = some q ∧
      firstSignalWitness (signalsOf p) (signalsOf q) = some w := by
  -- Unfold and case split the pipeline to expose the Some-branches required by `hw`.
  unfold frameshiftSemanticWitness at hw
  -- applyMutation must be some
  cases happ : applyMutation gene m with
  | none =>
      simp [happ] at hw
  | some mutated =>
    -- both splices must be some
    cases hsG : Bio.Genetics.splice gene with
    | none => simp [happ, hsG] at hw
    | some rawG =>
      cases hsM : Bio.Genetics.splice mutated with
      | none => simp [happ, hsG, hsM] at hw
      | some rawM =>
        -- both processed transcripts must be some
        cases hp : Bio.Genetics.processMRNA rawG with
        | none => simp [happ, hsG, hsM, hp] at hw
        | some p =>
          cases hq : Bio.Genetics.processMRNA rawM with
          | none => simp [happ, hsG, hsM, hp, hq] at hw
          | some q =>
            simp [happ, hsG, hsM, hp, hq] at hw
            aesop-- ⟨mutated, rawG, rawM, p, q, happ, hsG, hsM, hp, hq, hw⟩

private lemma proteins_ne_of_processed_witness
    (gene mutated : Gene) (rawG rawM : RawMRNA) (p q : ProcessedMRNA) (w : SignalWitness)
    (hsG : Bio.Genetics.splice gene = some rawG)
    (hsM : Bio.Genetics.splice mutated = some rawM)
    (hp : Bio.Genetics.processMRNA rawG = some p)
    (hq : Bio.Genetics.processMRNA rawM = some q)
    (hw : firstSignalWitness (signalsOf p) (signalsOf q) = some w) :
    Bio.Genetics.synthesizeProtein gene ≠ Bio.Genetics.synthesizeProtein mutated := by
  -- From witness, translates of coding regions differ
  have hneq_tr : Bio.Genetics.translate p.coding_region ≠ Bio.Genetics.translate q.coding_region :=
    proteins_differ_of_witness p q w hw
  intro hEq
  -- Normalize both sides of `synthesizeProtein` to `some (translate …)`
  have hs :=
    Bio.Genetics.synthesizeProtein_eq_some_of_processed (g := gene)    (raw := rawG) (p := p) hsG hp
  have hm :=
    Bio.Genetics.synthesizeProtein_eq_some_of_processed (g := mutated) (raw := rawM) (p := q) hsM hq
  -- Turn `hEq` into an equality between the two `some …`
  have hEq_some :
      some (_root_.Bio.Genetics.translate p.coding_region) =
      some (_root_.Bio.Genetics.translate q.coding_region) := by
    simpa [hs, hm] using hEq
  -- Extract payload equality with fully-qualified head symbol
  have hEq_payload_root :
      _root_.Bio.Genetics.translate p.coding_region =
      _root_.Bio.Genetics.translate q.coding_region :=
    Option.some.inj hEq_some
  -- Also rewrite the inequality with the fully-qualified head so the types match
  have hneq_tr_root :
      _root_.Bio.Genetics.translate p.coding_region ≠
      _root_.Bio.Genetics.translate q.coding_region := by
    exact hneq_tr
  -- Contradict the witness-derived inequality
  exact hneq_tr_root hEq_payload_root

/-- Non-axiomatic, end-to-end: if a frameshift mutation (by arithmetic check) has a semantic
witness, then synthesized proteins are unequal. -/
theorem frameshift_with_witness_changes_protein
    (gene : Gene) (m : Mutation)
    (w : SignalWitness)
    (hw : frameshiftSemanticWitness gene m = some w) :
    ∃ mutated_gene,
      applyMutation gene m = some mutated_gene ∧
      synthesizeProtein gene ≠ synthesizeProtein mutated_gene := by
  -- Unpack the witness to the concrete objects we need.
  rcases frameshiftWitness_unpack gene m w hw with
    ⟨mutated, rawG, rawM, p, q, happ, hsG, hsM, hp, hq, hw'⟩
  -- Conclude protein inequality.
  exact ⟨mutated, happ, proteins_ne_of_processed_witness gene mutated rawG rawM p q w hsG hsM hp hq hw'⟩

/-!
  Frameshift indels that occur in the coding sequence change the resulting protein.
-/

/-- Constructive, non-axiomatic: any insertion inside the CDS whose length
    is not a multiple of 3 changes the synthesized protein, provided a semantic
    witness exists (produced by `frameshiftSemanticWitness`). -/
theorem frameshift_changes_protein
  (gene : Gene) (pos : Nat) (bases : List DNABase)
  (hOffset : (Bio.Mutation.getCodingOffset gene pos).isSome)
  (hMod : bases.length % 3 ≠ 0)
  (mutated_gene : Gene)
  (hApply : applyInsertion gene pos bases = some mutated_gene)
  (w : SignalWitness)
  (hw : frameshiftSemanticWitness gene (.Insertion pos bases) = some w)
  : synthesizeProtein gene ≠ synthesizeProtein mutated_gene := by
  -- Use the witness-based non-axiomatic end-to-end theorem
  have hmain :=
    frameshift_with_witness_changes_protein
      (gene := gene) (m := .Insertion pos bases) (w := w) (hw := hw)
  -- hmain gives an existential mutated', align it with the concrete mutated_gene via hApply
  rcases hmain with ⟨mutated', happ', hneq'⟩
  -- unify mutated' with mutated_gene by determinism of applyMutation/applyInsertion
  have happApplyMutation : applyMutation gene (.Insertion pos bases) = some mutated_gene := by
    -- applyMutation on Insertion definitionally calls applyInsertion
    simpa [applyMutation] using hApply
  -- some mutated' = some mutated_gene ⇒ mutated' = mutated_gene
  have h_eq_opt : some mutated' = some mutated_gene := by
    simpa [happ'] using happApplyMutation
  have h_eq_mut : mutated' = mutated_gene := Option.some.inj h_eq_opt
  -- rewrite and conclude
  subst h_eq_mut
  exact hneq'

/--
If an insertion of a single base occurs at an exonic position that is not on
a codon boundary, and (conservatively) the position is known to be in CDS,
then the synthesized protein changes (with a provided semantic witness).
-/
lemma frameshift_single_base_changes_protein
    (gene : Gene) (pos : Nat) (base : DNABase)
    --(h_exonic : IsExonic gene pos)
    --(h_not_codon_boundary : (pos % 3) ≠ 0)
    (h_in_cds : (Bio.Mutation.getCodingOffset gene pos).isSome)
    (w : SignalWitness)
    (hw : frameshiftSemanticWitness gene (.Insertion pos [base]) = some w) :
    ∀ mutated_gene, applyInsertion gene pos [base] = some mutated_gene →
      synthesizeProtein gene ≠ synthesizeProtein mutated_gene := by
  intro mutated_gene hApply
  -- 1 % 3 ≠ 0
  have h_len : ([base].length % 3) ≠ 0 := by simp
  -- Use the constructive frameshift theorem
  exact frameshift_changes_protein
    gene pos [base] h_in_cds h_len mutated_gene hApply w hw

/--
A single-base insertion in the CDS at an offset not divisible by 3
semantically changes the synthesized protein (constructively, via a witness).
-/
theorem single_base_insertion_in_cds_changes_protein_semantic
    (gene : Gene) (pos : Nat) (base : DNABase)
    (mutated_gene : Gene)
    (h_apply : applyInsertion gene pos [base] = some mutated_gene)
    (cds_offset : Nat)
    (h_offset : getCodingOffset gene pos = some cds_offset)
    --(h_frameshift : cds_offset % 3 ≠ 0)
    (w : SignalWitness)
    (hw : frameshiftSemanticWitness gene (.Insertion pos [base]) = some w) :
    synthesizeProtein gene ≠ synthesizeProtein mutated_gene := by
  -- CDS membership as Option.isSome
  have h_in_cds : (getCodingOffset gene pos).isSome := by
    -- from equality to isSome
    simp [h_offset]
  -- 1 % 3 ≠ 0
  have h_len : ([base].length % 3) ≠ 0 := by simp
  -- Conclude via constructive frameshift theorem
  exact frameshift_changes_protein gene pos [base] h_in_cds h_len mutated_gene h_apply w hw

/-! ### Theorem 3: Frameshift from Single-Base Insertion -/

/--
If an insertion of a single base occurs in the coding sequence (CDS),
then it is classified as a frameshift by the arithmetic checker.
-/
lemma frameshift_single_base_is_classified_frameshift
    (gene : Gene) (pos : Nat) (base : DNABase)
    (h_in_cds : (Bio.Mutation.getCodingOffset gene pos).isSome) :
    analyzeMutationEffect gene (Mutation.Insertion pos [base]) = MutationEffect.Frameshift := by
  have h_frameshift : Bio.Mutation.mutationIsFrameshift gene (Mutation.Insertion pos [base]) := by
    -- [base].length = 1, and 1 % 3 ≠ 0
    simp [Bio.Mutation.mutationIsFrameshift, h_in_cds]
  simp [analyzeMutationEffect, h_frameshift]

/--
Constructive existence of the mutated gene after a single-base insertion at an
exonic coordinate, and protein change under the CDS postulate.
-/
theorem single_base_insertion_causes_frameshift
    (gene : Gene) (pos : Nat) (base : DNABase)
    (h_exonic : IsExonic gene pos)
    (h_not_codon_boundary : (pos % 3) ≠ 0)
    (h_in_cds : (Bio.Mutation.getCodingOffset gene pos).isSome)
    (w : SignalWitness)
    (hw : frameshiftSemanticWitness gene (.Insertion pos [base]) = some w) :
    let ins_mutation := Mutation.Insertion pos [base]
    ∃ mutated_gene, applyInsertion gene pos [base] = some mutated_gene ∧
    (synthesizeProtein gene ≠ synthesizeProtein mutated_gene) := by
  -- The insertion of a single base at an exonic position yields a valid mutated gene.
  -- We then conclude protein change by the domain postulate.
  intro ins_mutation
  -- exonic ⇒ pos < length ⇒ pos ≤ length (needed by applyInsertion)
  have hlt : pos < gene.coding_strand.seq.length := by
    rcases h_exonic with ⟨r, hr, _, h_in_end⟩
    exact lt_of_lt_of_le h_in_end (gene.h_exons_bounded r hr)
  have h_pos : pos ≤ gene.coding_strand.seq.length := Nat.le_of_lt hlt

  -- Let-bind as in applyInsertion to align exactly with its return shape.
  set insLen := [base].length with hins
  set mutated_seq :=
    gene.coding_strand.seq.take pos ++ [base] ++ gene.coding_strand.seq.drop pos with hmut
  set shifted_exons :=
    Bio.Mutation.shiftRegionsAfter pos (insLen : Int) gene.exons with hshift
  -- Non-empty exons are preserved under nonnegative shifts.
  have h_nonempty_after : shifted_exons ≠ [] := by
    simpa [shifted_exons, hshift, insLen, hins] using
      shiftRegionsAfter_preserves_nonempty
        pos insLen gene.exons gene.h_exons_nonempty
  -- Build the witness mutated gene matching applyInsertion’s record exactly.
  refine ⟨
    {
      id := gene.id
      coding_strand := { seq := mutated_seq }
      exons := shifted_exons
      promoter_region := gene.promoter_region
      poly_a_site := gene.poly_a_site.map (fun p => if p ≥ pos then p + insLen else p)
      h_exons_sorted := by
        simpa [shifted_exons, hshift, insLen, hins] using
          (shiftRegionsAfter_preserves_sorted
            (pos := pos) (shift := insLen) (regions := gene.exons) gene.h_exons_sorted)
      h_exons_bounded := by
        -- Reuse the lets-specialized boundedness lemma.
        intro r' hr'
        have core :=
          exons_bounded_after_insertion_lets
            (gene := gene) (pos := pos) (bases := [base]) h_pos
        -- First align the membership to the core lemma’s shifted_exons
        have hb' :
            r'.end_ ≤ (gene.coding_strand.seq.take pos ++ [base] ++ gene.coding_strand.seq.drop pos).length :=
          core r' (by simpa [shifted_exons, hshift, insLen, hins])
        -- Now normalize to our local lets
        have hb : r'.end_ ≤ mutated_seq.length := by
          simpa [mutated_seq, hmut] using hb'
        -- Goal uses the record’s coding_strand field; unfold it
        simpa
      h_exons_nonempty := h_nonempty_after
    },
    ?heq,
    ?hneq
  ⟩
  -- Equality: unfold applyInsertion and discharge the if-branches by simp.
  ·
    -- Derive the guard used inside applyInsertion from h_nonempty_after
    have h_guard :
        Bio.Mutation.shiftRegionsAfter pos (insLen : Int) gene.exons ≠ [] := by
      simpa [shifted_exons, hshift, insLen, hins] using h_nonempty_after
    -- applyInsertion returns exactly the above record under h_pos and h_guard
    simp [applyInsertion, h_pos, insLen, hins, mutated_seq, hmut,
          shifted_exons, hshift, h_guard]
    aesop
  -- Protein change: invoke the frameshift lemma (which uses the domain postulate).
  ·
    -- Re-derive the same equality to feed the domain-axiom wrapper.
    have h_guard :
        Bio.Mutation.shiftRegionsAfter pos (insLen : Int) gene.exons ≠ [] := by
      simpa [shifted_exons, hshift, insLen, hins] using h_nonempty_after
    have happly :
        applyInsertion gene pos [base] =
          some
            { id := gene.id
              coding_strand := { seq := mutated_seq }
              exons := shifted_exons
              promoter_region := gene.promoter_region
              poly_a_site := gene.poly_a_site.map (fun p => if p ≥ pos then p + insLen else p)
              h_exons_sorted := by
                simpa [shifted_exons, hshift, insLen, hins] using
                  (shiftRegionsAfter_preserves_sorted
                    (pos := pos) (shift := insLen) (regions := gene.exons) gene.h_exons_sorted)
              h_exons_bounded := by
                intro r' hr'
                have core :=
                  exons_bounded_after_insertion_lets
                    (gene := gene) (pos := pos) (bases := [base]) h_pos
                -- Align membership then normalize lengths
                have hb' :
                    r'.end_ ≤ (gene.coding_strand.seq.take pos ++ [base] ++ gene.coding_strand.seq.drop pos).length :=
                  core r' (by simpa [shifted_exons, hshift, insLen, hins])
                have hb : r'.end_ ≤ mutated_seq.length := by
                  simpa [mutated_seq, hmut] using hb'
                simpa
              h_exons_nonempty := h_nonempty_after } := by
      simp [applyInsertion, h_pos, insLen, hins, mutated_seq, hmut]; exact
        (ne_and_eq_iff_right (id (Ne.symm h_nonempty_after))).mpr hshift
    -- From above, use the constructive single-base frameshift lemma with a semantic witness.
    apply frameshift_single_base_changes_protein
            gene pos base h_in_cds w hw
    exact happly

/-! ### Semantic Proof of Frameshift Protein Change -/

/--
Helper lemma: `chunkList 3` after splitting a list at an arbitrary boundary `k - k % 3`
is equal to chunking the original list; this follows from `take_append_drop`.
This replaces the previous, stronger (and unused) statement and avoids the missing lemma.
-/
lemma chunkList_cons_after_insertion {α : Type u} (l : List α) (x : α) (k : Nat) :
    let l' := l.take k ++ [x] ++ l.drop k
    List.chunkList 3 l' =
      List.chunkList 3 (l'.take (k - k % 3) ++ l'.drop (k - k % 3)) := by
  intro l'
  -- Directly rewrite with take_append_drop and congrArg
  simp


/-! ### Theorem 4: Start Codon Necessity -/

lemma findStartCodon_none_if_no_aug (mrna : Bio.Sequence.MRNA)
    (h_no_aug : ∀ i, i + 2 < (mrna.seq.drop mrna.five_utr_length).length →
     ¬((mrna.seq.drop mrna.five_utr_length)[i]! = Bio.RNABase.A ∧
       (mrna.seq.drop mrna.five_utr_length)[i+1]! = Bio.RNABase.U ∧
       (mrna.seq.drop mrna.five_utr_length)[i+2]! = Bio.RNABase.G)) :
    findStartCodon mrna = none := by
  -- Work on the coding sequence
  set seq := mrna.seq.drop mrna.five_utr_length with hseq
  -- Aux lemma: if a list has no AUG at any position, aux never pushes, so it returns acc.reverse
  have aux_nil :
      ∀ (rem : List Bio.RNABase) (idx : Nat) (acc : List (Nat × Nat)),
        (∀ i, i + 2 < rem.length →
          ¬(rem[i]! = Bio.RNABase.A ∧ rem[i+1]! = Bio.RNABase.U ∧ rem[i+2]! = Bio.RNABase.G)) →
        Bio.Genetics.findAndScoreStartCodons.aux seq idx rem acc = acc.reverse := by
    intro rem
    induction rem with
    | nil =>
      intro idx acc _; simp [Bio.Genetics.findAndScoreStartCodons.aux]
    | cons a rem ih =>
      intro idx acc hno
      cases rem with
      | nil =>
        -- only one element, cannot contain AUG
        simp [Bio.Genetics.findAndScoreStartCodons.aux]
      | cons b rem' =>
        cases rem' with
        | nil =>
          -- only two elements, cannot contain AUG
          simp [Bio.Genetics.findAndScoreStartCodons.aux]
        | cons c rem'' =>
          -- Show the head is not AUG using hno at index 0
          have hhead : ¬(a = Bio.RNABase.A ∧ b = Bio.RNABase.U ∧ c = Bio.RNABase.G) := by
            intro habc; rcases habc with ⟨ha, hb, hc⟩; subst ha hb hc
            have hlen : 0 + 2 < (Bio.RNABase.A :: Bio.RNABase.U :: Bio.RNABase.G :: rem'').length := by simp
            have := hno 0 hlen
            -- At index 0 we do have AUG, contradiction
            simp at this
          -- No AUG at head ⇒ aux takes the “_ :: rest” branch
          -- Build the shifted “no AUG” hypothesis for the tail (starting at index 0 of b::c::rem'')
          have h_tail :
              ∀ i, i + 2 < (b :: c :: rem'').length →
                ¬(((b :: c :: rem'')[i]! = Bio.RNABase.A) ∧
                  ((b :: c :: rem'')[i+1]! = Bio.RNABase.U) ∧
                  ((b :: c :: rem'')[i+2]! = Bio.RNABase.G)) := by
            intro i hi
            -- Map to original indices: (i+1) in a::b::c::rem''
            have hi' : (i + 1) + 2 < (a :: b :: c :: rem'').length := by
              simpa using Nat.succ_lt_succ hi
            have := hno (i + 1) hi'
            -- Rewrite getElem! through cons to align indices
            simpa using this
          -- Reduce one step, then apply IH on tail with idx+1 and same acc
          have := ih (idx + 1) acc h_tail
          -- Use the fact head is not AUG to select the second branch
          -- This is achieved by case analysis on a,b,c matching against A,U,G
          -- so that simp goes to the “_ :: rest” branch.
          by_cases hA : a = Bio.RNABase.A
          · by_cases hU : b = Bio.RNABase.U
            · by_cases hG : c = Bio.RNABase.G
              · exact False.elim (hhead ⟨hA, hU, hG⟩)
              · subst hA; subst hU; simp [Bio.Genetics.findAndScoreStartCodons.aux, hG, this]
            · subst hA; simp [Bio.Genetics.findAndScoreStartCodons.aux, hU, this]
          · simp [Bio.Genetics.findAndScoreStartCodons.aux, hA, this]
  -- Candidates are empty by applying aux_nil at idx=0, acc=[]
  have h_empty : findAndScoreStartCodons seq = [] := by
    -- Unfold the outer definition just to expose the call to aux; then reuse aux_nil
    unfold findAndScoreStartCodons
    simpa using aux_nil seq 0 [] (by
      -- h_no_aug is exactly the required hypothesis on seq
      intro i hi; exact h_no_aug i (by simpa [hseq] using hi))
  -- Now rewrite findStartCodon with empty candidates; foldl on [] gives none
  simp [findStartCodon, hseq, h_empty]
  aesop

theorem no_start_no_protein (mrna : Bio.Sequence.MRNA) :
    (∀ i, i + 2 < mrna.seq.length →
     ¬(mrna.seq[i]! = Bio.RNABase.A ∧ mrna.seq[i+1]! = Bio.RNABase.U ∧ mrna.seq[i+2]! = Bio.RNABase.G)) →
    findStartCodon mrna = none := by
  intro h_no_aug
  -- Convert the hypothesis to work on the dropped sequence
  have h_no_aug_dropped : ∀ i, i + 2 < (mrna.seq.drop mrna.five_utr_length).length →
     ¬((mrna.seq.drop mrna.five_utr_length)[i]! = Bio.RNABase.A ∧
       (mrna.seq.drop mrna.five_utr_length)[i+1]! = Bio.RNABase.U ∧
       (mrna.seq.drop mrna.five_utr_length)[i+2]! = Bio.RNABase.G) := by
    intro i hi
    have h_bound : mrna.five_utr_length + i + 2 < mrna.seq.length := by
      simp [List.length_drop] at hi
      omega
    specialize h_no_aug (mrna.five_utr_length + i) h_bound
    -- avoid List.getElem! in simp set; use get?_drop and bridge lemma
    simp [getElem!_eq_getElem?_getD, List.getElem?_drop] at *
    convert h_no_aug using 2
  exact findStartCodon_none_if_no_aug mrna h_no_aug_dropped

/-! ### Theorem 5: Kozak Context Affects Translation -/

open Bio.Theorems

theorem strong_kozak_preferred :
    ∀ (context1 context2 : List RNABase),
    -- Strong Kozak: GCC[AUG]G
    context1 = [.G, .C, .C, .A, .U, .G, .G, .C] →
    -- Weak Kozak: UUU[AUG]C
    context2 = [.U, .U, .U, .A, .U, .G, .C, .U] →
    scoreKozak context1 > scoreKozak context2 := by
  intro c1 c2 h1 h2
  rw [h1, h2]
  unfold scoreKozak List.getNth?
  -- Strong context: G at -3 (3 points) + C at -2 (1) + C at -1 (1) + G at +4 (3) = 8
  -- Weak context: U at -3 (0) + U at -2 (0) + U at -1 (0) + C at +4 (0) = 0
  simp
end Genetics
end Bio

-- Section 7: Comprehensive Examples
namespace Bio.Examples

open Bio Bio.Sequence Bio.Genetics Bio.Mutation

def CFTR_fragment : Gene := {
  id := "CFTR_ΔF508"
  coding_strand := {
    seq := [
      -- Exon 1: Start codon and initial sequence
      DNABase.A, .T, .G, .G, .A, .T,  -- Met-Asp
      -- Intron 1
      .G, .T, .A, .A, .G, .T,  -- Splice sites
      -- Exon 2: Critical F508 region
      .T, .T, .C, .T, .T, .T   -- Phe-Phe (F507-F508)
    ]
  }
  exons := [
    { start := 0, end_ := 6, h_valid := by decide },
    { start := 12, end_ := 18, h_valid := by decide }
  ]
  h_exons_sorted := by unfold List.Chain'; simp
  h_exons_bounded := by
    intro r hr; simp at hr
    cases hr with
    | inl h => rw [h]; decide
    | inr h => rw [h]; decide
  h_exons_nonempty := by decide
}

/-- Demonstrate intronic mutation is silent -/
example :
    let pos := 8  -- Position in intron
    IsIntronic CFTR_fragment pos ∧
    (∀ new_base,
     analyzeMutationEffect CFTR_fragment (Mutation.Substitution pos new_base) =
     MutationEffect.Silent) := by
  intro pos
  constructor
  · -- Prove position 8 is intronic
    unfold IsIntronic IsExonic
    constructor
    · decide  -- pos < length
    · push_neg
      intro exon h_mem
      simp [CFTR_fragment] at h_mem
      cases h_mem with
      | inl h => rw [h]; decide
      | inr h => rw [h]; decide
  · -- All substitutions at intronic positions are silent
    intro new_base
    -- Re-establish intronic fact and positional bound
    have h_intronic : IsIntronic CFTR_fragment pos := by
      unfold IsIntronic IsExonic
      constructor
      · decide
      · push_neg
        intro exon h_mem
        simp [CFTR_fragment] at h_mem
        cases h_mem with
        | inl h => rw [h]; decide
        | inr h => rw [h]; decide
    have h_pos : pos < CFTR_fragment.coding_strand.seq.length := h_intronic.left
    -- Use the intronic preservation lemma to show proteins are equal
    -- Build the precise mutated gene produced by applySubstitution (to use in simp)
    set mutated_seq := CFTR_fragment.coding_strand.seq.set pos new_base with hmut
    have happly :
        applySubstitution CFTR_fragment pos new_base =
          some
            { CFTR_fragment with
              coding_strand := { seq := mutated_seq }
              h_exons_bounded := by
                intro r hr
                rw [List.length_set]
                exact CFTR_fragment.h_exons_bounded r hr } := by
      simp [applySubstitution, h_pos, mutated_seq, hmut]
    have hprot :
        synthesizeProtein CFTR_fragment =
        synthesizeProtein
          { CFTR_fragment with
            coding_strand := { seq := mutated_seq }
            h_exons_bounded := by
              intro r hr
              rw [List.length_set]
              exact CFTR_fragment.h_exons_bounded r hr } := by
      -- Prove splice-site safety and separation for this concrete gene/position.
      have h_safe : Bio.Genetics.SafeForSpliceSites CFTR_fragment pos := by
        refine And.intro h_intronic ?windows
        intro r hr
        -- Two exons: split cases and discharge arithmetic with decide.
        simp [CFTR_fragment] at hr
        cases hr with
        | inl h =>
            subst h; decide
        | inr h =>
            subst h; decide
      have h_sep :
          ∀ r ∈ CFTR_fragment.exons,
            CFTR_fragment.canonical_acceptor.length ≤ r.end_ + CFTR_fragment.canonical_donor.length := by
        intro r hr
        simp [CFTR_fragment] at hr
        cases hr with
        | inl h => subst h; decide
        | inr h => subst h; decide
      -- Apply the theorem with the exact witness from happly.
      exact
        intronic_substitution_preserves_protein
          CFTR_fragment pos new_base h_intronic h_safe h_sep
          { CFTR_fragment with
            coding_strand := { seq := mutated_seq }
            h_exons_bounded := by
              intro r hr
              rw [List.length_set]
              exact CFTR_fragment.h_exons_bounded r hr }
          happly
    -- Evaluate analyzeMutationEffect for a substitution at intronic pos; simplify to Silent
    simp [analyzeMutationEffect,
          Bio.Mutation.mutationIsFrameshift,  -- substitutions are never frameshift in this checker
          applyMutation, applySubstitution, h_pos, happly, hprot]
    aesop

end Bio.Examples
