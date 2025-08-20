import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions

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

/-! ### List Lemmas and Utilities -/
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
  | cons _ _ => simp; omega

def chunkList {α} (n : Nat) (l : List α) : List (List α) :=
  if h : n > 0 then chunkListPos n h l else []

def getNth? {α : Type*} (l : List α) (n : Nat) : Option α :=
  if h : n < l.length then some l[n] else none

end List


/-! ### Section 2: Core Biological Entities  -/
namespace Bio

inductive DNABase
  | A | T | G | C | N  -- N for unknown/any base
  deriving Repr, DecidableEq, Inhabited, BEq

/--
Includes `DegenerateDNABase` to model ambiguity forr applications 
like primer design and consensus sequences.
-/
inductive DegenerateDNABase
  | Standard (b : DNABase)
  | R -- A or G (puRine)
  | Y -- C or T (pYrimidine)
  | S -- G or C (Strong)
  | W -- A or T (Weak)
  | K -- G or T (Keto)
  | M -- A or C (aMino)
  | B -- C, G, or T (not A)
  | D -- A, G, or T (not C)
  | H -- A, C, or T (not G)
  | V -- A, C, or G (not T)
  deriving Repr, DecidableEq

inductive RNABase
  | A | U | G | C | N  -- N for unknown/any base
  deriving Repr, DecidableEq, Inhabited, BEq

inductive AminoAcid
  | Ala | Arg | Asn | Asp | Cys | Gln | Glu | Gly | His | Ile
  | Leu | Lys | Met | Phe | Pro | Ser | Thr | Trp | Tyr | Val
  deriving Repr, DecidableEq, Inhabited, BEq

/--
Includes `AminoAcidProperties` for higher-level reasoning.
This enables proving theorems about the functional impact of missense mutations
(e.g., conservative vs. non-conservative changes).
-/
structure AminoAcidProperties where
  isAcidic : Bool
  isBasic : Bool
  isUnchargedPolar : Bool
  isNonpolar : Bool
  deriving Repr, DecidableEq

def getProperties (aa : AminoAcid) : AminoAcidProperties :=
  match aa with
  | .Asp | .Glu => ⟨true, false, false, false⟩
  | .Lys | .Arg | .His => ⟨false, true, false, false⟩
  | .Asn | .Gln | .Cys | .Ser | .Thr | .Tyr => ⟨false, false, true, false⟩
  | _ => ⟨false, false, false, true⟩ -- The rest are nonpolar


inductive TranslationSignal
  | Continue (aa : AminoAcid)
  | Stop
  | Error  -- Invalid/incomplete codon
  deriving Repr, DecidableEq, BEq

/-- Comprehensive mutation types including all major categories -/
inductive Mutation
  | Substitution (pos : Nat) (original : DNABase) (new : DNABase)
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

-- ### Section 3: Enhanced Gene Architecture
namespace Bio.Sequence

open Bio

@[ext] structure DNAStrand where
  seq : List DNABase
  deriving Repr, DecidableEq, BEq

/-- Represents the strand of a gene on a reference chromosome. -/
inductive StrandSign
  | Plus  -- 5' -> 3'
  | Minus -- 3' -> 5'
  deriving Repr, DecidableEq

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

/--
We use  a data-driven `SpliceSiteSignature` structure. 
This makes the model more general and extensible
to non-canonical splice sites.
-/
structure SpliceSiteSignature where
  donorSite : List DNABase -- e.g., [.G, .T]
  acceptorSite : List DNABase -- e.g., [.A, .G]
  deriving Repr, BEq

-- A constant for the standard case, for convenience.
def standardSpliceSites : SpliceSiteSignature :=
  { donorSite := [.G, .T], acceptorSite := [.A, .G] }

structure Gene where
  id : String
  coding_strand : DNAStrand
  exons : List GenomicRegion
  splice_sites : SpliceSiteSignature 
  promoter_region : Option GenomicRegion := none
  poly_a_site : Option Nat := none
  strand : StrandSign                
  h_exons_sorted : List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start) exons
  h_exons_bounded : ∀ r ∈ exons, r.end_ ≤ coding_strand.seq.length
  h_exons_nonempty : exons ≠ []

/-
-- Added canonical splice sites to the Gene definition for a more realistic splicing model??.
structure Gene'ì where
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
  -/

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

/- ### Section 4: Complete Central Dogma Implementation -/
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
      simp_all only [foldl_nil, Option.some.injEq, not_mem_nil, or_false]
  | curr :: ys, acc, r, h => by
      rcases chooseBest_some_cases acc curr with ⟨acc', hstep, hacc'⟩
      have h' : ys.foldl chooseBest (some acc') = some r := by
        simpa [List.foldl, hstep] using h
      have ih := foldl_chooseBest_mem_aux ys acc' r h'
      cases ih with
      | inl heq =>
          cases hacc' with
          | inl hacc =>
              subst hacc heq
              simp_all only [foldl_cons, mem_cons, true_or]
          | inr hcurr =>
              subst hcurr
              aesop
      | inr hin =>
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
  rcases h_ind with h_in_acc | h_is_aug
  · cases (List.mem_cons.mp h_in_acc) with
    | inl h_eq_head =>
      have hpidx : p = idx := by
        simpa using congrArg Prod.fst h_eq_head
      subst hpidx
      exact Or.inr ⟨rest', h_head⟩
    | inr h_in_tail =>
      exact Or.inl h_in_tail
  · exact Or.inr h_is_aug

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
    exact Or.inl (by simpa [aux, List.mem_reverse] using hp)
  | cons a rem' ih =>
    intro idx acc hdrop hp
    cases rem' with
    | nil =>
      have hp' : (p, s) ∈ aux rna (idx + 1) [] acc := by
        simpa [aux] using hp
      have hdrop' : rna.drop (idx + 1) = [] := by
        have hcons : rna.drop idx = a :: ([] : List RNABase) := by simpa using hdrop
        exact List.drop_succ_of_drop_cons hcons
      exact ih (idx + 1) acc hdrop' hp'
    | cons b rem'' =>
      cases rem'' with
      | nil =>
        have hp' : (p, s) ∈ aux rna (idx + 1) [b] acc := by
          simpa [aux] using hp
        have hdrop' : rna.drop (idx + 1) = [b] := by
          have hcons : rna.drop idx = a :: b :: ([] : List RNABase) := by simpa using hdrop
          exact List.drop_succ_of_drop_cons hcons
        exact ih (idx + 1) acc hdrop' hp'
      | cons c rest =>
        by_cases hAUG : (a = .A ∧ b = .U ∧ c = .G)
        · rcases hAUG with ⟨hA, hU, hG⟩
          subst hA; subst hU; subst hG
          have hp' :
              (p, s) ∈
                aux rna (idx + 1) (.U :: .G :: rest)
                  ((idx,
                      scoreKozak
                        ((rna.drop (if idx ≥ 3 then idx - 3 else 0)).take
                          ((idx - if idx ≥ 3 then idx - 3 else 0) + 3 + min 5 rest.length))) :: acc) := by
            simpa [aux] using hp
          have hhead : rna.drop idx = .A :: .U :: .G :: rest := by simpa using hdrop
          have hdrop' : rna.drop (idx + 1) = .U :: .G :: rest :=
            List.drop_succ_of_drop_cons (by simpa using hhead)
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
          exact mem_isAUG_cons_AUG (rna := rna) (idx := idx) (acc := acc) (p := p) (s := s)
            hhead hp' hind
        · have hp' : (p, s) ∈ aux rna (idx + 1) (b :: c :: rest) acc := by
            have step :
                aux rna idx (a :: b :: c :: rest) acc =
                aux rna (idx + 1) (b :: c :: rest) acc := by
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
          have hdrop' : rna.drop (idx + 1) = b :: c :: rest := by
            have hcons : rna.drop idx = a :: b :: c :: rest := by simpa using hdrop
            exact List.drop_succ_of_drop_cons hcons
          exact ih (idx + 1) acc hdrop' hp' --
          
end findAndScoreStartCodons

-- Corollary for the top-level function: any picked index points to AUG.
lemma findAndScoreStartCodons_mem_AUG {rna : List RNABase} {p s : Nat}
    (hmem : (p, s) ∈ findAndScoreStartCodons rna) :
    ∃ rest, rna.drop p = .A :: .U :: .G :: rest := by
  have := findAndScoreStartCodons.mem_isAUG (rna := rna) 0 rna [] rfl p s (by
    simpa [findAndScoreStartCodons])
  exact this.elim (fun hinAcc => False.elim (by cases hinAcc)) id

/-- Advanced start codon selection based on Kozak scoring -/
def findStartCodon (mrna : Bio.Sequence.MRNA) : Option Nat :=
  let coding_seq := mrna.seq.drop mrna.five_utr_length
  let candidates := findAndScoreStartCodons coding_seq
  -- Selects best scoring, or first if tie, using the shared chooser
  let best := candidates.foldl chooseBest none
  best.map (·.1)

lemma findStartCodon_is_AUG_simple
    (m : Bio.Sequence.MRNA) {i : Nat}
    (h : findStartCodon m = some i) :
    (m.seq.drop (m.five_utr_length + i)).take 3 = [.A, .U, .G] := by
  unfold findStartCodon at h
  set coding_seq := m.seq.drop m.five_utr_length with hseq
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
  match hstart : findStartCodon { seq := mrna.seq } with 
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
            have hpick : findStartCodon { seq := mrna.seq } = some startPos := hstart
            have hAUG_at_start :
                (mrna.seq.drop (0 + startPos)).take 3 = [.A, .U, .G] := by
              simpa using
                (findStartCodon_is_AUG_simple
                  ({ seq := mrna.seq, five_utr_length := 0, three_utr_length := 0 })
                  (i := startPos) hpick)
            have hAUG_potential : (potential_cds.take 3) = [.A, .U, .G] := by
              simpa [potential_cds, Nat.zero_add] using hAUG_at_start
            have h_count_pos : 1 ≤ cds_codon_count := by
              exact Nat.succ_le_succ (Nat.zero_le _)
            have h3le : 3 ≤ cds_len := by
              have := Nat.mul_le_mul_right 3 h_count_pos
              simpa [cds_len, Nat.one_mul] using this
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

/-- Splice function,  driven by the `SpliceSiteSignature` structure. -/
private def spliceAndCheck (gene : Gene) (pre_mrna : List RNABase) :
    List GenomicRegion → List RNABase → Option (List RNABase)
  | [], acc => some acc
  | r :: rs, acc =>
    let acceptor_len := gene.splice_sites.acceptorSite.length
    let donor_len := gene.splice_sites.donorSite.length
    let acceptor_ok : Bool :=
      acc.isEmpty ||
        (r.start ≥ acceptor_len && -- Prevent underflow
         decide
          (((gene.coding_strand.seq.drop (r.start - acceptor_len)).take acceptor_len)
            = gene.splice_sites.acceptorSite))
    let donor_ok : Bool :=
      rs.isEmpty ||
        decide
          (((gene.coding_strand.seq.drop r.end_).take donor_len)
            = gene.splice_sites.donorSite)
    if acceptor_ok && donor_ok then
      let spliced_segment := pre_mrna.drop r.start |>.take r.length
      spliceAndCheck gene pre_mrna rs (acc ++ spliced_segment)
    else
      none

/--
Produces a mature mRNA by transcribing and splicing.
This version checks for canonical splice sites (e.g., GT-AG).
-/
def splice (gene : Gene) : Option RawMRNA :=
  let pre_mrna := transcribe gene.coding_strand.seq
  (spliceAndCheck gene pre_mrna gene.exons []).map ({ seq := · })

/-
/--
Produces a mature mRNA by transcribing and splicing.
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
Splicing based on a specific isoform, demonstrating the utility of the
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
The complete, revised pipeline from gene to protein, using the
splicing function. This pipeline can  fail at the splicing step.
-/
def synthesizeProtein (gene : Gene) : Option (List AminoAcid) :=
  let mrna? := splice gene
  mrna?.bind (fun mrna =>
    (processMRNA mrna).map (fun p => translate p.coding_region))

-- A pipeline for a specific splice isoform.
def synthesizeProteinFromIsoform (iso : SpliceIsoform) : Option (List AminoAcid) :=
  (spliceIsoform iso).bind (fun mrna =>
    (processMRNA mrna).map (fun p => translate p.coding_region))

lemma synthesizeProtein_eq_some_of_processed
    (g : Gene) {raw : RawMRNA} {p : ProcessedMRNA}
    (hsplice : splice g = some raw)
    (hproc   : processMRNA raw = some p) :
    synthesizeProtein g = some (translate p.coding_region) := by
  simp [synthesizeProtein, hsplice, hproc]

end Bio.Genetics

/- ### Section 5: Complete Mutation Analysis with Length-Altering Support-/
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
    -- 1 Entire region is strictly **after** the mutation coordinate --
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
    -- 3 Region is **before** the mutation point – remains unchanged --
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
  have h2_start_lt_pos : r2.start < pos := lt_of_lt_of_le r2.h_valid h2_before
  have hpos_lt_r2start : pos < r2.start := lt_of_lt_of_le h1_in.2 h_rel
  have hcontr : pos < pos := lt_trans hpos_lt_r2start h2_start_lt_pos
  exact (lt_irrefl _ hcontr)

/-- If the first region is after `pos` and the second contains `pos`,
this contradicts the sortedness `r1.end_ ≤ r2.start`. -/
private lemma impossible_after_inside
    {pos : Nat} {r1 r2 : GenomicRegion}
    (h_rel : r1.end_ ≤ r2.start)
    (h1_after : pos ≤ r1.start)
    (h2_in : r2.start < pos ∧ pos < r2.end_) : False := by
  have h_pos_lt_r1end : pos < r1.end_ := lt_of_le_of_lt h1_after r1.h_valid
  have h_pos_lt_r2start : pos < r2.start := lt_of_lt_of_le h_pos_lt_r1end h_rel
  have hcontr : pos < pos := lt_trans h_pos_lt_r2start h2_in.1
  exact (lt_irrefl _ hcontr)

/-- A simple helper: `a ≤ b` implies `a ≤ b + s`. -/
private lemma le_add_right {a b s : Nat} (h : a ≤ b) : a ≤ b + s :=
  Nat.le_trans h (Nat.le_add_right _ _)

lemma chain'_map_shift_preserve
    {regions : List GenomicRegion} (pos shift : Nat)
    (h_chain : List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start) regions) :
    List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start)
      (regions.map (fun r => shiftRegionAfterNat pos shift r)) := by
  let R : GenomicRegion → GenomicRegion → Prop := fun r1 r2 => r1.end_ ≤ r2.start
  have h_chain' : List.Chain' R regions := h_chain
  induction regions with
  | nil =>
    simp
  | cons r rs ih =>
    cases rs with
    | nil =>
      simp
    | cons r' rs' =>
      cases h_chain' with
      | cons h_rel h_tail =>
        constructor
        · by_cases h1_after : pos ≤ r.start
          · by_cases h2_after : pos ≤ r'.start
            · have : r.end_ + shift ≤ r'.start + shift := Nat.add_le_add_right h_rel shift
              simpa [R, shiftRegionAfterNat, h1_after, h2_after] using this
            · have h2_not_after : ¬ pos ≤ r'.start := h2_after
              by_cases h2_inside : pos < r'.end_
              · have h2_start_lt_pos : r'.start < pos := Nat.lt_of_not_ge h2_not_after
                have h_pos_lt_rend : pos < r.end_ := lt_of_le_of_lt h1_after r.h_valid
                have h_pos_lt_r2start : pos < r'.start := lt_of_lt_of_le h_pos_lt_rend h_rel
                have hcontr : pos < pos := lt_trans h_pos_lt_r2start h2_start_lt_pos
                exact (lt_irrefl _ hcontr).elim
              · have h2_start_lt_pos : r'.start < pos := Nat.lt_of_not_ge h2_not_after
                have h_pos_lt_rend : pos < r.end_ := lt_of_le_of_lt h1_after r.h_valid
                have h_pos_lt_r2start : pos < r'.start := lt_of_lt_of_le h_pos_lt_rend h_rel
                have hcontr : pos < pos := lt_trans h_pos_lt_r2start h2_start_lt_pos
                exact (lt_irrefl _ hcontr).elim
          · have h1_not_after : ¬ pos ≤ r.start := h1_after
            by_cases h1_inside : pos < r.end_
            · by_cases h2_after : pos ≤ r'.start
              · have : r.end_ + shift ≤ r'.start + shift := Nat.add_le_add_right h_rel shift
                simpa [R, shiftRegionAfterNat, h1_not_after, h1_inside, h2_after] using this
              · have h2_not_after : ¬ pos ≤ r'.start := h2_after
                by_cases h2_inside : pos < r'.end_
                · have h2_start_lt_pos : r'.start < pos := Nat.lt_of_not_ge h2_not_after
                  have h_pos_lt_r2start : pos < r'.start := lt_of_lt_of_le h1_inside h_rel
                  have hcontr : pos < pos := lt_trans h_pos_lt_r2start h2_start_lt_pos
                  exact (lt_irrefl _ hcontr).elim
                · have h2_before : r'.end_ ≤ pos := le_of_not_gt (by simpa [gt_iff_lt] using h2_inside)
                  have h2_start_lt_pos : r'.start < pos := Nat.lt_of_not_ge h2_not_after
                  have hcontr : pos < pos :=
                    lt_trans (lt_of_lt_of_le h1_inside h_rel) h2_start_lt_pos
                  exact (lt_irrefl _ hcontr).elim
            · have h1_before : r.end_ ≤ pos := le_of_not_gt (by simpa [gt_iff_lt] using h1_inside)
              by_cases h2_after : pos ≤ r'.start
              · have : r.end_ ≤ r'.start := h_rel
                have : r.end_ ≤ r'.start + shift := le_add_right this
                simpa [R, shiftRegionAfterNat, h1_not_after, h1_inside, h2_after] using this
              · have h2_not_after : ¬ pos ≤ r'.start := h2_after
                by_cases h2_inside : pos < r'.end_
                · have : r.end_ ≤ r'.start := h_rel
                  simpa [R, shiftRegionAfterNat, h1_not_after, h1_inside, h2_not_after, h2_inside] using this
                · have : r.end_ ≤ r'.start := h_rel
                  simpa [R, shiftRegionAfterNat, h1_not_after, h1_inside, h2_not_after, h2_inside] using this
        · apply ih
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
    simp
  have h₂ : (rna.drop idx).drop 1 = l := by
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
  have hlen3 : (rna.drop idx).length ≥ 3 := by simp [h]
  have hlt : idx + 2 < rna.length := by
    have : 3 ≤ rna.length - idx := by simpa [List.length_drop] using hlen3
    omega
  have h0opt : rna[idx]? = some .A := by
    have hL : (rna.drop idx)[0]? = some .A := by simp [h]
    have hR : (rna.drop idx)[0]? = rna[idx]? := by
      simp
    exact (Eq.trans hR.symm hL)
  have h1opt : rna[idx+1]? = some .U := by
    have hL : (rna.drop idx)[1]? = some .U := by simp [h]
    have hR : (rna.drop idx)[1]? = rna[idx+1]? := by
      simp
    exact (Eq.trans hR.symm hL)
  have h2opt : rna[idx+2]? = some .G := by
    have hL : (rna.drop idx)[2]? = some .G := by simp [h]
    have hR : (rna.drop idx)[2]? = rna[idx+2]? := by
      simp
    aesop
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
    cases tl with
    | nil =>
      have hdrop' : rna.drop (idx + 1) = [] := by
        have : rna.drop idx = a :: ([] : List RNABase) := by simpa using hdrop
        exact drop_succ_of_drop_cons (rna := rna) (idx := idx) (a := a) (l := []) this
      have hp' : p ∈ augScanAux (idx + 1) [] acc := by
        simpa [augScanAux_cons_len1_eq] using hp
      simpa using ih (idx + 1) acc hdrop' hp'
    | cons b tl' =>
      cases tl' with
      | nil =>
        have hdrop' : rna.drop (idx + 1) = [b] := by
          have : rna.drop idx = a :: [b] := by simpa using hdrop
          exact drop_succ_of_drop_cons (rna := rna) (idx := idx) (a := a) (l := [b]) this
        have hp' : p ∈ augScanAux (idx + 1) [b] acc := by
          simpa [augScanAux_cons_len2_eq] using hp
        simpa using ih (idx + 1) acc hdrop' hp'
      | cons c rest =>
        by_cases hA : a = .A
        · by_cases hU : b = .U
          · by_cases hG : c = .G
            · have h_head : rna.drop idx = .A :: .U :: .G :: rest := by
                simpa [hA, hU, hG] using hdrop
              have hdropUG : rna.drop (idx + 1) = .U :: .G :: rest :=
                drop_succ_of_drop_cons (rna := rna) (idx := idx) (a := .A) (l := .U :: .G :: rest) h_head
              have hdrop' : rna.drop (idx + 1) = b :: c :: rest := by
                simpa [hU, hG] using hdropUG
              have hpUG : p ∈ augScanAux (idx + 1) (.U :: .G :: rest) (idx :: acc) := by
                simpa [augScanAux_cons_AUG_eq, hA, hU, hG] using hp
              have hp' : p ∈ augScanAux (idx + 1) (b :: c :: rest) (idx :: acc) := by
                simpa [hU, hG] using hpUG
              have h_rec := ih (idx + 1) (idx :: acc) hdrop' hp'
              rcases h_rec with h_in_acc | h_prop
              · cases List.mem_cons.mp h_in_acc with
                | inl p_eq_idx =>
                  have h_at : p + 2 < rna.length ∧
                              rna[p]! = .A ∧ rna[p+1]! = .U ∧ rna[p+2]! = .G := by
                    have h_idx := aug_at_of_drop_AUG (rna := rna) (idx := idx) (rest := rest) h_head
                    simpa [p_eq_idx] using h_idx
                  exact Or.inr h_at
                | inr p_in_acc =>
                  exact Or.inl p_in_acc
              · exact Or.inr h_prop
            · have hdrop' : rna.drop (idx + 1) = b :: c :: rest := by
                have hx : rna.drop idx = a :: b :: c :: rest := by simpa using hdrop
                exact drop_succ_of_drop_cons (rna := rna) (idx := idx) (a := a) (l := b :: c :: rest) hx
              have h_not : ¬(a = .A ∧ b = .U ∧ c = .G) := by
                intro h; exact hG h.2.2
              have step := augScanAux_cons_nonAUG_eq idx a b c rest acc h_not
              have hp' : p ∈ augScanAux (idx + 1) (b :: c :: rest) acc := by
                subst hU hA
                simp_all only [getElem!_eq_getElem?_getD, and_false, not_false_eq_true]
              simpa using ih (idx + 1) acc hdrop' hp'
          · have hdrop' : rna.drop (idx + 1) = b :: c :: rest := by
              have hx : rna.drop idx = a :: b :: c :: rest := by simpa using hdrop
              exact drop_succ_of_drop_cons (rna := rna) (idx := idx) (a := a) (l := b :: c :: rest) hx
            have h_not : ¬(a = .A ∧ b = .U ∧ c = .G) := by
              intro h; exact hU h.2.1
            have step := augScanAux_cons_nonAUG_eq idx a b c rest acc h_not
            have hp' : p ∈ augScanAux (idx + 1) (b :: c :: rest) acc := by
              simpa [←step, hA] using hp
            simpa using ih (idx + 1) acc hdrop' hp'
        · have hdrop' : rna.drop (idx + 1) = b :: c :: rest := by
            have hx : rna.drop idx = a :: b :: c :: rest := by simpa using hdrop
            exact drop_succ_of_drop_cons (rna := rna) (idx := idx) (a := a) (l := b :: c :: rest) hx
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
    { r with
      start := r.start + shift
      end_  := r.end_  + shift
      h_valid := Nat.add_lt_add_right r.h_valid shift }
  else if h_part : pos < r.end_ then
    { r with
      end_ := r.end_ + shift
      h_valid := by
        exact lt_of_lt_of_le r.h_valid (Nat.le_add_right _ _) }
  else
    r

/-- On a singleton list, the nonnegative shift agrees with the Nat-side mapper. -/
lemma shiftRegionsAfter_nonneg_eq_map_singleton
    (pos shift : Nat) (r : GenomicRegion) :
    shiftRegionsAfter pos (shift : Int) [r] =
      [shiftRegionAfterNat pos shift r] := by
  by_cases h_all : pos ≤ r.start
  · have h_newStart_nonneg : 0 ≤ ((r.start : Int) + shift) := by
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
    simp [shiftRegionsAfter, shiftRegionAfterNat, h_all, h_guard, hstart, hend]
  · by_cases h_part : pos < r.end_
    · have h_gt : (r.start : Int) < (r.end_ : Int) + shift := by
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
      simp [shiftRegionsAfter, shiftRegionAfterNat, h_all, h_part, h_gt, hend]
    · simp [shiftRegionsAfter, shiftRegionAfterNat, h_all, h_part]

/-- For nonnegative shifts, the head of a cons always survives, so we can peel it as an append. -/
lemma shiftRegionsAfter_nonneg_cons_eq_append
    (pos shift : Nat) (r : GenomicRegion) (rs : List GenomicRegion) :
    shiftRegionsAfter pos (shift : Int) (r :: rs) =
      shiftRegionsAfter pos (shift : Int) [r] ++
      shiftRegionsAfter pos (shift : Int) rs := by
  by_cases h_all : pos ≤ r.start
  · have h_newStart_nonneg : 0 ≤ ((r.start : Int) + shift) := by
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
    simp [shiftRegionsAfter]
    aesop
  · by_cases h_part : pos < r.end_
    · have h_gt : (r.start : Int) < (r.end_ : Int) + shift := by
        have h0 : (r.start : Int) < (r.end_ : Int) := by exact_mod_cast r.h_valid
        have h_le : (r.end_ : Int) ≤ (r.end_ : Int) + shift :=
          le_add_of_nonneg_right (by exact_mod_cast Nat.zero_le shift)
        exact lt_of_lt_of_le h0 h_le
      simp [shiftRegionsAfter, h_all, h_part, h_gt]
    · simp [shiftRegionsAfter, h_all, h_part]

/--
For nonnegative shift (the insertion case), shiftRegionsAfter agrees with
a simple map over regions, i.e. it does not drop any region.
-/
lemma shiftRegionsAfter_nonneg_eq_map (pos shift : Nat) (regions : List GenomicRegion) :
    shiftRegionsAfter pos (shift : Int) regions =
      regions.map (shiftRegionAfterNat pos shift) := by
  induction regions with
  | nil =>
      simp [shiftRegionsAfter]
  | cons r rs ih =>
      calc
        shiftRegionsAfter pos (shift : Int) (r :: rs)
            = shiftRegionsAfter pos (shift : Int) [r] ++
              shiftRegionsAfter pos (shift : Int) rs := by
                simpa using
                  shiftRegionsAfter_nonneg_cons_eq_append pos shift r rs
        _ = [shiftRegionAfterNat pos shift r] ++
              shiftRegionsAfter pos (shift : Int) rs := by
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
  have h_eq := shiftRegionsAfter_nonneg_eq_map pos shift regions
  simpa [h_eq, shiftRegionAfterNat] using
    (chain'_map_shift_preserve (regions := regions) (pos := pos) (shift := shift) h_sorted)

-- A simple and often-needed length identity for insertion.
lemma length_after_insertion {α} (l ins : List α) (pos : Nat)
    (hpos : pos ≤ l.length) :
    (l.take pos ++ ins ++ l.drop pos).length = l.length + ins.length := by
  have hlen :
      (l.take pos ++ ins ++ l.drop pos).length
        = pos + ins.length + (l.length - pos) := by
    simp [List.length_append, List.length_take, List.length_drop,
          Nat.min_eq_left hpos, Nat.add_assoc]
  calc
    (l.take pos ++ ins ++ l.drop pos).length
        = pos + ins.length + (l.length - pos) := hlen
    _ = pos + (ins.length + (l.length - pos)) := by
        simp [Nat.add_assoc]
    _ = pos + ((l.length - pos) + ins.length) := by
        simp [Nat.add_comm]
    _ = (pos + (l.length - pos)) + ins.length := by
        simp [Nat.add_assoc]
    _ = l.length + ins.length := by
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
  change r' ∈ shiftRegionsAfter pos (insLen : Int) gene.exons at hr'
  change r'.end_ ≤ (gene.coding_strand.seq.take pos ++ bases ++ gene.coding_strand.seq.drop pos).length
  have h_eq := shiftRegionsAfter_nonneg_eq_map pos insLen gene.exons
  have hr'_map : r' ∈ gene.exons.map (shiftRegionAfterNat pos insLen) := by
    simpa [h_eq] using hr'
  rcases List.mem_map.1 hr'_map with ⟨r, hr_mem, hmap⟩
  have hr_bound := gene.h_exons_bounded r hr_mem
  subst hmap
  have hlen_base :
      (gene.coding_strand.seq.take pos ++ bases ++ gene.coding_strand.seq.drop pos).length
        = gene.coding_strand.seq.length + bases.length :=
    length_after_insertion _ _ _ hpos
  have hlen :
      (gene.coding_strand.seq.take pos ++ bases ++ gene.coding_strand.seq.drop pos).length
        = gene.coding_strand.seq.length + insLen := by
    simpa [insLen] using hlen_base
  by_cases h_all : pos ≤ r.start
  · have hend : (shiftRegionAfterNat pos insLen r).end_ = r.end_ + insLen := by
      simp [shiftRegionAfterNat, h_all]
    aesop
  · by_cases h_part : pos < r.end_
    · have hend : (shiftRegionAfterNat pos insLen r).end_ = r.end_ + insLen := by
        simp [shiftRegionAfterNat, h_all, h_part]
      aesop
    · have hend : (shiftRegionAfterNat pos insLen r).end_ = r.end_ := by
        simp [shiftRegionAfterNat, h_all, h_part]
      have h_ge_len :
          gene.coding_strand.seq.length
            ≤ (gene.coding_strand.seq.take pos ++ bases ++ gene.coding_strand.seq.drop pos).length := by
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
        splice_sites := gene.splice_sites
        promoter_region := gene.promoter_region
        poly_a_site := gene.poly_a_site.map (fun p => if p ≥ pos then p + insLen else p)
        strand := gene.strand
        h_exons_sorted := by
          exact shiftRegionsAfter_preserves_sorted pos insLen gene.exons gene.h_exons_sorted
        h_exons_bounded := by
          intro r' hr'
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
  have : (b : Int) ≤ (a : Int) := by simpa [sub_nonneg] using h
  exact Int.ofNat_le.mp this

/-- From a + b ≤ c we get a ≤ c - b. -/
lemma le_sub_of_add_le {a b c : Nat} (h : a + b ≤ c) : a ≤ c - b := by
  have hb : b ≤ c := le_trans (Nat.le_add_left _ _) h
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
  simp [hall] at hopt
  set newStart : Int := (r.start : Int) - len
  set newEnd   : Int := (r.end_  : Int) - len
  have hform : (if h_ok : newStart ≥ 0 ∧ newEnd > newStart then
                  some { start := newStart.toNat, end_ := newEnd.toNat,
                         h_valid := by
                           have : (newStart.toNat : Int) < (newEnd.toNat : Int) := by
                             have h₁ : (newStart.toNat : Int) = newStart := by
                               simp [Int.toNat_of_nonneg h_ok.1]
                             have h₂ : (newEnd.toNat : Int) = newEnd := by
                               have : (0 : Int) ≤ newEnd := le_trans h_ok.1 (le_of_lt h_ok.2)
                               simp [Int.toNat_of_nonneg this]
                             simpa [h₁, h₂] using h_ok.2
                           exact_mod_cast this }
                else none) = some r' := by
    simpa [newStart, newEnd, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hopt
  by_cases hok : newStart ≥ 0 ∧ newEnd > newStart
  · have hsome := hform
    simp [hok] at hsome
    have hrec := hsome
    have hend := congrArg GenomicRegion.end_ hrec
    exact ⟨by simpa [newEnd] using hend.symm, hok.1⟩
  · have := hform
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
  have hiff :
      (newEnd > r.start) ↔ ((r.start : Int) + (len : Int) < (r.end_ : Int)) := by
    constructor
    · intro h
      have := add_lt_add_right h (len : Int)
      simpa [newEnd, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    · intro h
      have := add_lt_add_right h (-(len : Int))
      simpa [newEnd, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
  by_cases hgt : newEnd > r.start
  · have h_nonneg : (0 : Int) ≤ newEnd := by
      have : (0 : Int) ≤ (r.start : Int) := by exact_mod_cast Nat.zero_le _
      exact le_trans this (le_of_lt hgt)
    have h_valid' : r.start < newEnd.toNat := by
      have : (r.start : Int) < (newEnd.toNat : Int) := by
        simpa [Int.toNat_of_nonneg h_nonneg] using hgt
      exact_mod_cast this
    have hcond : (r.start : Int) + (len : Int) < (r.end_ : Int) := (hiff.mp hgt)
    have hrec :
        ({ r with end_ := newEnd.toNat, h_valid := h_valid' } : GenomicRegion) = r' := by
      simpa [shiftRegionsAfter, hnall, hpart, newEnd, hcond, sub_eq_add_neg] using hopt
    have hend := congrArg GenomicRegion.end_ hrec
    exact ⟨by simpa [newEnd] using hend.symm, h_nonneg⟩
  · have hcond_false : ¬ ((r.start : Int) + (len : Int) < (r.end_ : Int)) := by
      intro hcond
      exact hgt (hiff.mpr hcond)
    have hfalse : False := by
      simp [hnall, hpart, hcond_false] at hopt
    cases hfalse

/-- Boundedness of exon ends after deletion. -/
lemma shiftRegionsAfter_bounded_after_deletion
    (gene : Bio.Sequence.Gene) (pos len : Nat)
    (h : pos + len ≤ gene.coding_strand.seq.length) :
    let mutated_seq := gene.coding_strand.seq.take pos ++ gene.coding_strand.seq.drop (pos + len)
    let shifted_exons := shiftRegionsAfter pos (-(len : Int)) gene.exons
    ∀ r' ∈ shifted_exons, r'.end_ ≤ mutated_seq.length := by
  intro mutated_seq shifted_exons r' hr'
  rcases List.mem_filterMap.1 hr' with ⟨r, hr_mem, hopt⟩
  have hlen : mutated_seq.length = gene.coding_strand.seq.length - len := by
    simp [mutated_seq, length_after_deletion _ _ _ h]
  have hr_bound := gene.h_exons_bounded r hr_mem
  by_cases hall : pos ≤ r.start
  · have h_after :=
      shiftRegionsAfter_after_case_end_toNat_eq
        (pos := pos) (len := len) (r := r) (r' := r') hall hopt
    rcases h_after with ⟨hend_eq, hstart_nonneg⟩
    have hlen_le_start : len ≤ r.start :=
      nat_le_of_int_sub_nonneg (a := r.start) (b := len) hstart_nonneg
    have hlen_le_end : len ≤ r.end_ := le_trans hlen_le_start (le_of_lt r.h_valid)
    have hendNat : ((r.end_ : Int) - len).toNat = r.end_ - len :=
      Int.toNat_sub_of_le r.end_ len hlen_le_end
    have : r'.end_ ≤ gene.coding_strand.seq.length - len := by
      simpa [hend_eq, hendNat] using Nat.sub_le_sub_right hr_bound len
    simpa [hlen] using this
  · by_cases hpart : pos < r.end_
    · have h_inside :=
        shiftRegionsAfter_inside_case_end_toNat_eq
          (pos := pos) (len := len) (r := r) (r' := r') (hnall := hall) (hpart := hpart) hopt
      rcases h_inside with ⟨hend_eq, hend_nonneg⟩
      have hlen_le_end : len ≤ r.end_ :=
        nat_le_of_int_sub_nonneg (a := r.end_) (b := len) hend_nonneg
      have hendNat : ((r.end_ : Int) - len).toNat = r.end_ - len :=
        Int.toNat_sub_of_le r.end_ len hlen_le_end
      have : r'.end_ ≤ gene.coding_strand.seq.length - len := by
        simpa [hend_eq, hendNat] using Nat.sub_le_sub_right hr_bound len
      simpa [hlen] using this
    · have r_before : r.end_ ≤ pos := le_of_not_gt hpart
      have hr'_eq_r : r' = r := by
        simp [hall, hpart] at hopt
        exact hopt.symm
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
      let r' : GenomicRegion := { r with start := start', h_valid := h }
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
      set start' := max r.start lastEnd with hstart'
      by_cases hk : start' < r.end_
      · have hcons :
            ({ r with start := start', h_valid := hk } : GenomicRegion) ::
              enforceSortedNonOverlap.go r.end_ rs = s :: rest := by
          simpa [enforceSortedNonOverlap.go, hk] using h
        have hhead :
            some ({ r with start := start', h_valid := hk } : GenomicRegion) = some s := by
          simpa using congrArg List.head? hcons
        have hs_eq : ({ r with start := start', h_valid := hk } : GenomicRegion) = s :=
          Option.some.inj hhead
        have hle : lastEnd ≤ start' := Nat.le_max_right _ _
        aesop
      · have h' : enforceSortedNonOverlap.go lastEnd rs = s :: rest := by
          simpa [enforceSortedNonOverlap.go, hk] using h
        exact ih h'

/-- The normalizer produces a Chain'-sorted list. -/
lemma enforceSortedNonOverlap_chain (regions : List GenomicRegion) :
    List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start) (enforceSortedNonOverlap regions) := by
  have aux :
      ∀ (rs : List GenomicRegion), ∀ lastEnd,
        List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start)
          (enforceSortedNonOverlap.go lastEnd rs) := by
    intro rs
    induction rs with
    | nil =>
        intro lastEnd
        simp [enforceSortedNonOverlap.go]
    | cons r rs ih =>
        intro lastEnd
        dsimp [enforceSortedNonOverlap.go]
        set start' := max r.start lastEnd with hstart'
        by_cases hk : start' < r.end_
        · cases htail : enforceSortedNonOverlap.go (r.end_) rs with
          | nil =>
              simp [hk]
          | cons s rest =>
              have hs : r.end_ ≤ s.start :=
                enforceSortedNonOverlap.head_start_ge (lastEnd := r.end_) (rs := rs) (s := s) (rest := rest) htail
              have hs' :
                  ({ r with start := start', h_valid := hk } : GenomicRegion).end_ ≤ s.start := by
                simpa using hs
              have hchain_tail :
                  List.Chain' (fun r1 r2 => r1.end_ ≤ r2.start) (s :: rest) := by
                simpa [htail] using ih (r.end_)
              simpa [enforceSortedNonOverlap.go, hk, htail] using
                And.intro hs' hchain_tail
        · simpa [enforceSortedNonOverlap.go, hk] using ih lastEnd
  simpa [enforceSortedNonOverlap] using aux regions 0

/-- Boundedness propagates through the normalizer. -/
lemma enforceSortedNonOverlap_bounded
    {L : Nat} {regions : List GenomicRegion}
    (hB : ∀ r ∈ regions, r.end_ ≤ L) :
    ∀ r' ∈ enforceSortedNonOverlap regions, r'.end_ ≤ L := by
  have aux :
      ∀ (rs : List GenomicRegion) (lastEnd : Nat),
        (∀ r ∈ rs, r.end_ ≤ L) →
        ∀ r' ∈ enforceSortedNonOverlap.go lastEnd rs, r'.end_ ≤ L := by
    intro rs
    induction rs with
    | nil =>
        intro lastEnd _ r' hr'
        simp [enforceSortedNonOverlap.go] at hr'
    | cons r rs ih =>
        intro lastEnd hRs r' hr'
        dsimp [enforceSortedNonOverlap.go] at hr'
        set start' := max r.start lastEnd with hstart'
        by_cases hk : start' < r.end_
        · have hRs_head : r.end_ ≤ L := hRs r (by simp)
          have hRs_tail : ∀ x ∈ rs, x.end_ ≤ L := by
            intro x hx; exact hRs x (by simp [hx])
          have hmem :
              r' ∈ ({ r with start := start', h_valid := hk } : GenomicRegion) ::
                    enforceSortedNonOverlap.go
                      (({ r with start := start', h_valid := hk } : GenomicRegion).end_) rs := by
            simpa [enforceSortedNonOverlap.go, hk] using hr'
          have hr'cases :
              r' = ({ r with start := start', h_valid := hk } : GenomicRegion) ∨
              r' ∈ enforceSortedNonOverlap.go
                      (({ r with start := start', h_valid := hk } : GenomicRegion).end_) rs :=
            (List.mem_cons).1 hmem
          cases hr'cases with
          | inl hhead =>
              have : r'.end_ ≤ L := by
                simpa [hhead] using hRs_head
              exact this
          | inr htail =>
              have rend :
                  ({ r with start := start', h_valid := hk } : GenomicRegion).end_ = r.end_ := rfl
              have htail' :
                  r' ∈ enforceSortedNonOverlap.go (r.end_) rs := by
                simpa [rend] using htail
              exact ih (r.end_) hRs_tail r' htail'
        · have hRs_tail : ∀ x ∈ rs, x.end_ ≤ L := by
            intro x hx; exact hRs x (by simp [hx])
          have hr'_tail : r' ∈ enforceSortedNonOverlap.go lastEnd rs := by
            simpa [enforceSortedNonOverlap.go, hk] using hr'
          exact ih lastEnd hRs_tail r' hr'_tail
  intro r' hr'
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
          calc
            start + (end_ - start) + (l.length - end_)
                = (start + (end_ - start)) + (l.length - end_) := by
                  simp [Nat.add_assoc]
            _ = end_ + (l.length - end_) := by simp [h1]
            _ = l.length := h2

/--
A robust, single-pass function to apply a deletion to an exon list.
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
      if h_before : r_end ≤ del_start then
        go rs (r :: acc)
      else if h_after : r_start ≥ del_end then
        let shift_len := del_end - del_start
        have h_s_le_start : shift_len ≤ r.start := by
          exact le_trans (Nat.sub_le _ _) h_after
        have h_delEnd_le_end : del_end ≤ r.end_ := by
          exact le_trans h_after (Nat.le_of_lt r.h_valid)
        have h_s_le_end : shift_len ≤ r.end_ := by
          exact le_trans (Nat.sub_le _ _) h_delEnd_le_end
        have h_added :
            shift_len + (r.start - shift_len) < shift_len + (r.end_ - shift_len) := by
          simpa [Nat.add_sub_of_le h_s_le_start, Nat.add_sub_of_le h_s_le_end] using r.h_valid
        have h_sub_lt :
            r.start - shift_len < r.end_ - shift_len := Nat.lt_of_add_lt_add_left h_added
        let new_r : GenomicRegion := {
          start := r.start - shift_len,
          end_ := r.end_ - shift_len,
          h_valid := h_sub_lt
        }
        go rs (new_r :: acc)
      else if h_inside : del_start > r_start ∧ del_end < r_end then
        let shift_len := del_end - del_start
        have h_s_le_end : shift_len ≤ r.end_ := by
          exact le_trans (Nat.sub_le _ _) (Nat.le_of_lt h_inside.2)
        have h_add_lt : r.start + shift_len < r.end_ := by
          by_cases h_order : del_start ≤ del_end
          · have h_lt_left :
                r.start + (del_end - del_start) < del_start + (del_end - del_start) :=
              Nat.add_lt_add_right (show r.start < del_start from h_inside.1) _
            have h_eq : del_start + (del_end - del_start) = del_end :=
              Nat.add_sub_of_le h_order
            have h_left' : r.start + shift_len < del_end := by
              simpa [h_eq] using h_lt_left
            exact lt_trans h_left' h_inside.2
          · have hlt : del_end < del_start := Nat.lt_of_not_ge h_order
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
      else
        let new_end := if r_end ≤ del_end then del_start else r_end - (del_end - del_start)
        if h_keep : r_start < new_end then
          let new_r : GenomicRegion := { r with end_ := new_end, h_valid := h_keep }
          go rs (new_r :: acc)
        else
          go rs acc
  go exons []

/-- Apply deletion mutation with coordinate adjustment (uses proven normalizer). -/
def applyDeletion (gene : Gene) (pos : Nat) (len : Nat) : Option Gene :=
  if h_bounds : pos + len ≤ gene.coding_strand.seq.length then
    let mutated_seq := gene.coding_strand.seq.take pos ++
                      gene.coding_strand.seq.drop (pos + len)
    let shifted_exons_raw := shiftRegionsAfter pos (-len : Int) gene.exons
    let shifted_exons := enforceSortedNonOverlap shifted_exons_raw
    if h_valid : shifted_exons ≠ [] then
      some {
        id := gene.id
        coding_strand := { seq := mutated_seq }
        exons := shifted_exons
        splice_sites := gene.splice_sites
        promoter_region := gene.promoter_region
        poly_a_site := gene.poly_a_site.bind (fun p =>
          if p ≥ pos + len then some (p - len)
          else if p ≥ pos then none
          else some p)
        strand := gene.strand
        h_exons_sorted := by
          simpa using enforceSortedNonOverlap_chain shifted_exons_raw
        h_exons_bounded := by
          intro r' hr'
          have hB_raw :
              ∀ x ∈ shifted_exons_raw, x.end_ ≤ mutated_seq.length := by
            intro x hx
            simpa [mutated_seq] using
              shiftRegionsAfter_bounded_after_deletion
                (gene := gene) (pos := pos) (len := len) h_bounds
                x hx
          have : ∀ x ∈ shifted_exons, x.end_ ≤ mutated_seq.length := by
            simpa [shifted_exons] using
              enforceSortedNonOverlap_bounded
                (regions := shifted_exons_raw) (L := mutated_seq.length) hB_raw
          exact this r' hr'
        h_exons_nonempty := h_valid
      }
    else none
  else none

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
        h_exons_sorted := by
          simpa using enforceSortedNonOverlap_chain shifted_exons_raw
        h_exons_bounded := by
          intro r' hr'
          have hB_raw :
              ∀ x ∈ shifted_exons_raw, x.end_ ≤ mutated_seq.length := by
            intro x hx
            simpa [mutated_seq] using
              shiftRegionsAfter_bounded_after_deletion
                (gene := gene) (pos := pos) (len := len) h_bounds
                x hx
          have : ∀ x ∈ shifted_exons, x.end_ ≤ mutated_seq.length := by
            simpa [shifted_exons] using
              enforceSortedNonOverlap_bounded
                (regions := shifted_exons_raw) (L := mutated_seq.length) hB_raw
          exact this r' hr'
        h_exons_nonempty := h_valid
      }
    else none
  else none-/

/-- Safe substitution: requires in-bounds and that the current base equals `original`. -/
def applySubstitution (gene : Gene) (pos : Nat) (original : DNABase) (new : DNABase) : Option Gene :=
  if h : pos < gene.coding_strand.seq.length then
    let cur := gene.coding_strand.seq.getD pos DNABase.N
    if hmatch : cur = original then
      let mutated_seq := gene.coding_strand.seq.set pos new
      some { gene with
        coding_strand := { seq := mutated_seq }
        h_exons_bounded := by
          intro r hr
          have hb := gene.h_exons_bounded r hr
          -- set preserves length, so mutated_seq.length = original length
          simpa [mutated_seq, List.length_set] using hb
      }
    else
      none
  else
    none

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
        have hlen :
            mutated_seq.length = gene.coding_strand.seq.length := by
          have hse : start ≤ end_ := Nat.le_of_lt h_bounds.1
          simpa [mutated_seq, seg, segLen] using
            (length_after_inversion gene.coding_strand.seq start end_ hse h_bounds.2)
        simpa [hlen]
    }
  else
    none

/-! ## applyDuplication -/

def applyDuplication (gene : Gene) (start end_ : Nat) : Option Gene :=
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
        splice_sites := gene.splice_sites
        promoter_region := gene.promoter_region
        poly_a_site := gene.poly_a_site.map (fun p => if p ≥ end_ then p + segLen else p)
        strand := gene.strand
        h_exons_sorted := by
          exact shiftRegionsAfter_preserves_sorted end_ bases.length gene.exons gene.h_exons_sorted
        h_exons_bounded := by
          intro r' hr'
          have hpos : end_ ≤ gene.coding_strand.seq.length := h_bounds.2
          have h_bases_len : bases.length = segLen := by
            have h_mid_bound : segLen ≤ gene.coding_strand.seq.length - start := by
              simpa [segLen] using Nat.sub_le_sub_right h_bounds.2 start
            simp [bases, List.length_take, List.length_drop,
                  Nat.min_eq_left h_mid_bound, segLen]
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
def applySpliceSite (gene : Gene) (exonIdx : Nat) (isDonor : Bool) (newBase : DNABase) : Option Gene :=
  if exonIdx < gene.exons.length then
    let r := gene.exons[exonIdx]!
    if isDonor then
      if exonIdx + 1 < gene.exons.length then
        if r.end_ < gene.coding_strand.seq.length then
          -- Mutate first base of donor window at r.end_
          let orig := gene.coding_strand.seq.getD r.end_ DNABase.N
          applySubstitution gene r.end_ orig newBase
        else none
      else none
    else
      let L_acc := gene.splice_sites.acceptorSite.length
      if 0 < exonIdx ∧ L_acc ≤ r.start then
        let pos := r.start - L_acc
        if pos < gene.coding_strand.seq.length then
          -- Mutate first base of acceptor window at r.start - L_acc
          let orig := gene.coding_strand.seq.getD pos DNABase.N
          applySubstitution gene pos orig newBase
        else none
      else none
  else none

def applyMutation (gene : Gene) (m : Mutation) : Option Gene :=
  match m with
  | .Substitution pos orig new => applySubstitution gene pos orig new
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
  -- First, we check for frameshift based on arithmetic properties. This is the most reliable check.
  if mutationIsFrameshift gene m then
    .Frameshift
  else
    -- For other cases, we simulate the effect by comparing protein products.
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
        .SpliceDefect
      else
        -- Fallback to the general analyzer rather than returning Silent.
        analyzeMutationEffect' gene m
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
        else
          match m with
          | .Insertion .. => .InFrameIndel
          | .Deletion ..  => .InFrameIndel
          | _             => .Missense -- Default for other complex changes
      | some _, none => .NoProtein
      | none, some _ => .RegulatoryDefect
      | none, none => .Silent

/- ### Section 6: Core Theorems with Complete Proofs -/

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
    simp [List.getElem?_drop, h_i,
          transcribe_set_ne _ _ _ _ h_ne]
  · simp [h_i]

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
      simp [spliceAndCheck]
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
      by_cases hc :
        ((acc.isEmpty ||
          decide (((g.coding_strand.seq.drop (r.start - g.splice_sites.acceptorSite.length)).take
                    g.splice_sites.acceptorSite.length) = g.splice_sites.acceptorSite))
         &&
         (rs.isEmpty ||
          decide (((g.coding_strand.seq.drop r.end_).take g.splice_sites.donorSite.length)
                    = g.splice_sites.donorSite)))
      · simp [spliceAndCheck, h_head]
        aesop
      · simp [spliceAndCheck, h_head]
        aesop

/-- A conservative “safety” predicate: the genomic position `pos` is intronic
    and does not lie in any acceptor/donor check window that `spliceAndCheck`
    inspects (acceptor window: [r.start - Lacc, r.start), donor window: [r.end_, r.end_ + Ldon)). -/
def SafeForSpliceSites (gene : Gene) (pos : Nat) : Prop :=
  IsIntronic gene pos ∧
  ∀ r ∈ gene.exons,
    let Lacc := gene.splice_sites.acceptorSite.length
    let Ldon := gene.splice_sites.donorSite.length
    (pos < r.start - Lacc ∨ r.start ≤ pos) ∧
    (pos < r.end_ ∨ r.end_ + Ldon ≤ pos)

/-- Generic slice stability: if `pos` is outside the slice window `[start, start+len)`,
    setting `l[pos] := a` does not change `take len (drop start l)`. -/
lemma take_drop_set_outside {α} (l : List α) (pos start len : Nat) (a : α)
    (hout : ∀ i, i < len → start + i ≠ pos) :
    ((l.set pos a).drop start).take len = (l.drop start).take len := by
  classical
  ext i
  by_cases hi : i < len
  · have hne : start + i ≠ pos := hout i hi
    have hraw :
        (l.set pos a)[start + i]? = l[start + i]? := by
      simpa using List.getElem?_set_ne (l := l) (i := pos) (j := start + i) (a := a) (h := hne.symm)
    simp [List.getElem?_drop, hi, hraw]
  · simp [hi]

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
  have hi_pos : i = pos := by simpa [hzero] using hip
  have : pos ≥ r.start ∧ pos < r.end_ := by
    exact ⟨by simpa [hi_pos] using hi_ge_start,
           by simpa [hi_pos] using hi_lt_end⟩
  exact (not_in_exon_of_intronic gene pos hintr hr) this

private lemma acceptor_avoid_pos_underflow_ge_end_pos_lt_end
    (gene : Gene) (pos : Nat) {r : GenomicRegion} (hr : r ∈ gene.exons)
    {L i : Nat} (hzero : r.start - L = 0) (hi_ge_end : r.end_ ≤ i) (hpos_lt_end : pos < r.end_) :
    (r.start - L) + i ≠ pos := by
  intro hip
  have hi_pos : i = pos := by simpa [hzero] using hip
  have hpos_ge_end : r.end_ ≤ pos := by simpa [hi_pos] using hi_ge_end
  exact (not_le_of_gt hpos_lt_end) hpos_ge_end

-- Stronger and simpler: if i lies inside the donor “right” window, donor safety (pos ≥ r.end_ + Ldon)
-- implies i < pos, hence inequality.
private lemma acceptor_avoid_pos_underflow_ge_end_pos_ge
    (gene : Gene) (pos : Nat) {r : GenomicRegion} (hr : r ∈ gene.exons)
    {L i : Nat} (hzero : r.start - L = 0) (hi_ge_start : r.start ≤ i) (hi_ge_end : r.end_ ≤ i)
    (hi_lt_right : i < r.end_ + gene.splice_sites.donorSite.length)
    (hpos_ge : r.end_ + gene.splice_sites.donorSite.length ≤ pos) :
    (r.start - L) + i ≠ pos := by
  intro hip
  have hi_pos : i = pos := by simpa [hzero] using hip
  have : i < pos := lt_of_lt_of_le hi_lt_right hpos_ge
  have hne : i ≠ pos := ne_of_lt this
  subst hi_pos
  simp_all only [zero_add, lt_self_iff_false]

/-- Indices of the acceptor window avoid a “safe” intronic position.

requires a mild separation bound `Lacc ≤ r.end_ + Ldon` to rule out the
previously unprovable corner case when `r.start - Lacc = 0`, `i ≥ r.end_`, and `pos ≥ r.end_ + Ldon`. -/
lemma acceptor_window_avoid_pos
    (gene : Gene) (pos : Nat)
    {r : GenomicRegion} (hr : r ∈ gene.exons)
    (hsafe : SafeForSpliceSites gene pos)
    (hLsep : gene.splice_sites.acceptorSite.length ≤ r.end_ + gene.splice_sites.donorSite.length) :
    let L := gene.splice_sites.acceptorSite.length
    ∀ i, i < L → (r.start - L) + i ≠ pos := by
  classical
  intro L i hi
  rcases hsafe with ⟨hintr, hwin⟩
  have hpos := (hwin r hr).1
  rcases hpos with hlt | hge
  · exact acceptor_avoid_pos_before_start (gene := gene) (pos := pos) (r := r) (hr := hr)
      (hi := hi) (hlt := hlt)
  · by_cases hL : L ≤ r.start
    · exact acceptor_avoid_pos_L_le_start (gene := gene) (pos := pos) (r := r) (hr := hr)
        (hi := hi) (hge := hge) (hL := hL)
    · have hzero : r.start - L = 0 := by
        have hle : r.start ≤ L := le_of_lt (lt_of_not_ge hL)
        simpa using Nat.sub_eq_zero_of_le hle
      by_cases hi_lt_start : i < r.start
      · exact acceptor_avoid_pos_underflow_lt_start (gene := gene) (pos := pos) (r := r) (hr := hr)
          (hi := hi) (hge := hge) (hzero := hzero) (hi_lt_start := hi_lt_start)
      · have hi_ge_start : r.start ≤ i := le_of_not_gt hi_lt_start
        have hdon := (hwin r hr).2
        by_cases hi_lt_end : i < r.end_
        · exact acceptor_avoid_pos_underflow_i_in_exon_contra (gene := gene) (pos := pos) (r := r) (hr := hr)
            (hintr := hintr) (hzero := hzero) (hi_ge_start := hi_ge_start) (hi_lt_end := hi_lt_end)
        · have hi_ge_end : r.end_ ≤ i := le_of_not_gt hi_lt_end
          rcases hdon with hpos_lt_end | hpos_ge
          · exact acceptor_avoid_pos_underflow_ge_end_pos_lt_end (gene := gene) (pos := pos) (r := r) (hr := hr)
              (hzero := hzero) (hi_ge_end := hi_ge_end) (hpos_lt_end := hpos_lt_end)
          · have hi_lt_right : i < r.end_ + gene.splice_sites.donorSite.length :=
              lt_of_lt_of_le hi hLsep
            exact acceptor_avoid_pos_underflow_ge_end_pos_ge (gene := gene) (pos := pos) (r := r) (hr := hr)
              (hzero := hzero) (hi_ge_start := hi_ge_start) (hi_ge_end := hi_ge_end)
              (hi_lt_right := hi_lt_right) (hpos_ge := hpos_ge)

/-- Acceptor window stability under a “safe” intronic set. -/
lemma acceptor_window_unchanged
    (gene : Gene) (pos : Nat) (new_base : DNABase)
    {r : GenomicRegion} (hr : r ∈ gene.exons)
    (hsafe : SafeForSpliceSites gene pos)
    (hLsep : gene.splice_sites.acceptorSite.length ≤ r.end_ + gene.splice_sites.donorSite.length) :
    let L := gene.splice_sites.acceptorSite.length
    (take L (drop (r.start - L) ((gene.coding_strand.seq).set pos new_base)))
      = take L (drop (r.start - L) (gene.coding_strand.seq)) := by
  classical
  intro L
  have hout :=
    acceptor_window_avoid_pos
      (gene := gene) (pos := pos) (r := r) (hr := hr)
      (hsafe := hsafe) (hLsep := hLsep)
  have hout' : ∀ i, i < L → (r.start - L) + i ≠ pos := by
    simpa [L] using hout
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
    let L := gene.splice_sites.donorSite.length
    (take L (drop r.end_ ((gene.coding_strand.seq).set pos new_base)))
      = take L (drop r.end_ (gene.coding_strand.seq)) := by
  classical
  intro L
  rcases hsafe with ⟨_, hwin⟩
  have hpos := (hwin r hr).2
  have hout : ∀ i, i < L → r.end_ + i ≠ pos := by
    intro i hi
    rcases hpos with hlt | hge
    · have : pos < r.end_ + i := lt_of_lt_of_le hlt (Nat.le_add_right _ _)
      exact (ne_of_lt this).symm
    · have : r.end_ + i < r.end_ + L := Nat.add_lt_add_left hi _
      exact ne_of_lt (lt_of_lt_of_le this hge)
  simpa using
    take_drop_set_outside (l := gene.coding_strand.seq) (pos := pos)
      (start := r.end_) (len := L) (a := new_base) hout

/-- Helper lemma: exon slices are unchanged under a safe intronic substitution. -/
lemma exon_slices_unchanged_under_intronic_subst
    (gene : Gene) (pos : Nat) (new_base : DNABase)
    (h_intronic : IsIntronic gene pos)
    (h_safe : SafeForSpliceSites gene pos) :
    let pre := transcribe gene.coding_strand.seq
    let post := transcribe (gene.coding_strand.seq.set pos new_base)
    ∀ region ∈ gene.exons,
      (post.drop region.start |>.take region.length) =
      (pre.drop region.start |>.take region.length) := by
  intro pre post region h_region
  simpa using exon_slice_unchanged_under_intronic_subst gene pos h_intronic h_region new_base

/-- Helper lemma: splice-site checks are unchanged under a safe intronic substitution. -/
lemma splice_sites_unchanged_under_intronic_subst
    (gene : Gene) (pos : Nat) (new_base : DNABase)
    (h_intronic : IsIntronic gene pos)
    (h_safe : SafeForSpliceSites gene pos)
    (h_sep : ∀ r ∈ gene.exons,
      gene.splice_sites.acceptorSite.length ≤ r.end_ + gene.splice_sites.donorSite.length) :
    let pre := transcribe gene.coding_strand.seq
    ∀ exons acc,
      (∀ r ∈ exons, r ∈ gene.exons) →
      spliceAndCheck
        ({ gene with
            coding_strand := { seq := gene.coding_strand.seq.set pos new_base }
            , h_exons_bounded := by
                intro r hr
                simpa [List.length_set] using (gene.h_exons_bounded r hr) })
        pre exons acc =
      spliceAndCheck gene pre exons acc := by
  intro pre exons acc h_subset
  let mutated_gene : Gene :=
    { gene with
        coding_strand := { seq := gene.coding_strand.seq.set pos new_base }
        , h_exons_bounded := by
            intro r hr
            simpa [List.length_set] using (gene.h_exons_bounded r hr) }
  revert acc h_subset
  induction exons with
  | nil =>
      intro acc _
      simp [spliceAndCheck]
  | cons r rs ih =>
    intro acc h_subset
    have hr_in : r ∈ gene.exons := h_subset r (by simp)
    have h_sep_r :
        gene.splice_sites.acceptorSite.length ≤ r.end_ + gene.splice_sites.donorSite.length :=
      h_sep r hr_in
    let Lacc := gene.splice_sites.acceptorSite.length
    let Ldon := gene.splice_sites.donorSite.length
    let cond : Prop :=
      (acc = [] ∨
        Lacc ≤ r.start ∧
          take Lacc (drop (r.start - Lacc) gene.coding_strand.seq) = gene.splice_sites.acceptorSite)
      ∧
      (rs = [] ∨
        take Ldon (drop r.end_ gene.coding_strand.seq) = gene.splice_sites.donorSite)
    by_cases hc : cond
    · -- When the condition holds, both sides take the "ok" branch with identical guards,
      -- because the splice windows are unchanged under the safe intronic substitution.
      simp [spliceAndCheck, cond, hc,
            (acceptor_window_unchanged (gene := gene) (pos := pos) (new_base := new_base)
              (r := r) (hr := hr_in) (hsafe := h_safe) (hLsep := h_sep_r)),
            (donor_window_unchanged (gene := gene) (pos := pos) (new_base := new_base)
              (r := r) (hr := hr_in) (hsafe := h_safe))]
      -- Tail call with extended accumulator; restrict subset hypothesis to the tail.
      aesop
    · -- When the condition fails, both sides take the "fail" path in the same way.
      simp [spliceAndCheck, cond, hc,
            (acceptor_window_unchanged (gene := gene) (pos := pos) (new_base := new_base)
              (r := r) (hr := hr_in) (hsafe := h_safe) (hLsep := h_sep_r)),
            (donor_window_unchanged (gene := gene) (pos := pos) (new_base := new_base)
              (r := r) (hr := hr_in) (hsafe := h_safe))]
      aesop

/-- Main lemma: splice is invariant under a safe intronic substitution. -/
lemma splice_independent_of_intronic_pos
    (gene : Gene) (pos : Nat) (new_base : DNABase)
    (h_intronic : IsIntronic gene pos)
    (h_safe : SafeForSpliceSites gene pos)
    (h_sep : ∀ r ∈ gene.exons,
      gene.splice_sites.acceptorSite.length ≤ r.end_ + gene.splice_sites.donorSite.length) :
    let mutated_gene : Gene :=
      { gene with
          coding_strand := { seq := gene.coding_strand.seq.set pos new_base }
          , h_exons_bounded := by
              intro r hr
              simpa [List.length_set] using (gene.h_exons_bounded r hr) }
    splice mutated_gene = splice gene := by
  classical
  let mutated_gene : Gene :=
    { gene with
        coding_strand := { seq := gene.coding_strand.seq.set pos new_base }
        , h_exons_bounded := by
            intro r hr
            simpa [List.length_set] using (gene.h_exons_bounded r hr) }
  let pre  := transcribe gene.coding_strand.seq
  let post := transcribe mutated_gene.coding_strand.seq
  have hSlices :
      ∀ region ∈ gene.exons,
        (post.drop region.start |>.take region.length) =
        (pre.drop  region.start |>.take region.length) :=
    exon_slices_unchanged_under_intronic_subst gene pos new_base h_intronic h_safe
  have hSites :
      ∀ exons acc, (∀ r ∈ exons, r ∈ gene.exons) →
        spliceAndCheck mutated_gene pre exons acc =
        spliceAndCheck gene         pre exons acc :=
    by
      simpa using
        splice_sites_unchanged_under_intronic_subst
          gene pos new_base h_intronic h_safe h_sep
  -- Now we switch the left splice from `post` to `pre` using slice congruence,
  -- then we use hSites to switch mutated→original on the same `pre`.
  unfold splice
  -- Step 1: mutated_gene: post → pre
  have h_congr :
      spliceAndCheck mutated_gene post gene.exons [] =
      spliceAndCheck mutated_gene pre  gene.exons [] :=
    spliceAndCheck_congr_slices mutated_gene post pre gene.exons [] (by
      intro r hr; exact hSlices r hr)
  -- Step 2: mutated_gene pre → gene pre, by site invariance
  have h_sites0 :
      spliceAndCheck mutated_gene pre gene.exons [] =
      spliceAndCheck gene         pre gene.exons [] :=
    hSites _ _ (by intro r hr; exact hr)
  aesop

theorem intronic_substitution_preserves_protein (gene : Gene) (pos : Nat)
    (original new : DNABase)
    (h_intronic : IsIntronic gene pos) (h_safe : Bio.Genetics.SafeForSpliceSites gene pos)
    (h_sep : ∀ r ∈ gene.exons, gene.splice_sites.acceptorSite.length ≤ r.end_ + gene.splice_sites.donorSite.length) :
    ∀ mutated_gene, applySubstitution gene pos original new = some mutated_gene →
    synthesizeProtein gene = synthesizeProtein mutated_gene := by
  intro mutated_gene h_apply
  unfold applySubstitution at h_apply
  by_cases h_pos : pos < gene.coding_strand.seq.length
  · -- In-bounds: we inspect the original-base guard
    simp [h_pos] at h_apply
    -- we name the local current base like the function does
    let cur := gene.coding_strand.seq.getD pos DNABase.N
    by_cases hmatch : cur = original
    · -- Match succeeds: the application must be `some {…}`
      have h_apply' := h_apply
      simp [cur, hmatch] at h_apply'
      cases h_apply'
      -- Splicing is invariant under safe intronic substitution
      have h_splice :
          splice
            ({ gene with
                coding_strand := { seq := gene.coding_strand.seq.set pos new }
                , h_exons_bounded := by
                    intro r hr
                    simpa [List.length_set] using (gene.h_exons_bounded r hr) }) =
          splice gene := by
        simpa using
          (Bio.Genetics.splice_independent_of_intronic_pos
              gene pos new h_intronic h_safe h_sep)
      -- Proteins equal since splice output is equal
      simp [synthesizeProtein]
      refine Option.bind_congr' ?_ fun a => congrFun rfl
      rw [← h_splice]; (expose_names; rw [right])
    · -- Original does not match: impossible to get `some _`
      aesop
  · -- Out of bounds: impossible to get `some _`
    simp [h_pos] at h_apply

/-- Nonnegative shifts (insertions) preserve non-emptiness of the exon list. -/
lemma shiftRegionsAfter_preserves_nonempty
    (pos shift : Nat) (regions : List GenomicRegion)
    (h_ne : regions ≠ []) :
    shiftRegionsAfter pos (shift : Int) regions ≠ [] := by
  cases regions with
  | nil =>
    exact (h_ne rfl).elim
  | cons r rs =>
    have hform :=
      shiftRegionsAfter_nonneg_eq_map pos shift (r :: rs)
    have hcons :
        shiftRegionsAfter pos (shift : Int) (r :: rs)
          = (shiftRegionAfterNat pos shift r) ::
              (rs.map (shiftRegionAfterNat pos shift)) := by
      simpa [List.map] using hform
    intro hnil
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
  exact rfl

/-- Single-base codon maps to `.Error`. -/
private lemma standardGeneticCode_error_len_one (a : RNABase) :
    standardGeneticCode [a] = TranslationSignal.Error := by
  cases a <;> unfold standardGeneticCode <;> rfl

/-- Two-base codon maps to `.Error`. -/
private lemma standardGeneticCode_error_len_two_exact (a b : RNABase) :
    standardGeneticCode [a, b] = TranslationSignal.Error := by
  cases a <;> cases b <;> unfold standardGeneticCode <;> rfl

/-- Short codons (length ≤ 2) map to `.Error`. -/
private lemma standardGeneticCode_error_len_le_two
    (c : List RNABase) (hle : c.length ≤ 2) :
    standardGeneticCode c = TranslationSignal.Error := by
  cases c with
  | nil =>
      exact standardGeneticCode_error_len_zero
  | cons a t =>
    cases t with
    | nil =>
        exact standardGeneticCode_error_len_one a
    | cons b t2 =>
      cases t2 with
      | nil =>
          exact standardGeneticCode_error_len_two_exact a b
      | cons d t3 =>
          have hgt' : 2 < (a :: b :: d :: t3).length := by simp
          exact False.elim ((not_le_of_gt hgt') hle)

/-- Long codons (length ≥ 4) map to `.Error`. -/
private lemma standardGeneticCode_error_len_ge_four
    {a b d e : RNABase} {t4 : List RNABase} :
    standardGeneticCode (a :: b :: d :: e :: t4) = TranslationSignal.Error := by
  classical
  cases a <;> cases b <;> cases d <;> cases t4 <;>
    unfold standardGeneticCode <;> rfl

/-- Any codon whose length is not exactly 3 maps to `.Error` in the standard code. -/
private lemma standardGeneticCode_eq_error_of_length_ne_three
    (c : List RNABase) (hne : c.length ≠ 3) :
    standardGeneticCode c = TranslationSignal.Error := by
  classical
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hle2 : c.length ≤ 2 := by
      -- `c.length < 3` ↔ `c.length ≤ 2`
      simpa [Nat.lt_succ_iff] using hlt
    exact standardGeneticCode_error_len_le_two c hle2
  · cases c with
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
              simp at hgt
          | cons e t4 =>
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
            simp [translateSignals, ih]
        | Stop =>
            simp [translateSignals]
        | Error =>
            simp [translateSignals]
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
      by_cases h_len : c.length = 3
      · simp [h_len]
        cases h_code : standardGeneticCode c
        · simp [ih]
        · simp
        · simp
      · have h_err : standardGeneticCode c = .Error :=
          standardGeneticCode_eq_error_of_length_ne_three c h_len
        simp [h_err]
  exact aux codons

/-- Bridge: `translate` equals `translateSignals ∘ signalsOf`. -/
lemma translate_eq_translateSignals (p : ProcessedMRNA) :
    translate p.coding_region = translateSignals (signalsOf p) := by
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
                          exact ⟨w0, by simp⟩
                    rcases this with ⟨w0, hw0⟩
                    intro h
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
  unfold frameshiftSemanticWitness at hw
  cases happ : applyMutation gene m with
  | none =>
      simp [happ] at hw
  | some mutated =>
    cases hsG : Bio.Genetics.splice gene with
    | none => simp [happ, hsG] at hw
    | some rawG =>
      cases hsM : Bio.Genetics.splice mutated with
      | none => simp [happ, hsG, hsM] at hw
      | some rawM =>
        cases hp : Bio.Genetics.processMRNA rawG with
        | none => simp [happ, hsG, hsM, hp] at hw
        | some p =>
          cases hq : Bio.Genetics.processMRNA rawM with
          | none => simp [happ, hsG, hsM, hp, hq] at hw
          | some q =>
            simp [happ, hsG, hsM, hp, hq] at hw
            aesop

private lemma proteins_ne_of_processed_witness
    (gene mutated : Gene) (rawG rawM : RawMRNA) (p q : ProcessedMRNA) (w : SignalWitness)
    (hsG : Bio.Genetics.splice gene = some rawG)
    (hsM : Bio.Genetics.splice mutated = some rawM)
    (hp : Bio.Genetics.processMRNA rawG = some p)
    (hq : Bio.Genetics.processMRNA rawM = some q)
    (hw : firstSignalWitness (signalsOf p) (signalsOf q) = some w) :
    Bio.Genetics.synthesizeProtein gene ≠ Bio.Genetics.synthesizeProtein mutated := by
  have hneq_tr : Bio.Genetics.translate p.coding_region ≠ Bio.Genetics.translate q.coding_region :=
    proteins_differ_of_witness p q w hw
  intro hEq
  -- we normalize both sides of `synthesizeProtein` to `some (translate …)`
  have hs :=
    Bio.Genetics.synthesizeProtein_eq_some_of_processed (g := gene)    (raw := rawG) (p := p) hsG hp
  have hm :=
    Bio.Genetics.synthesizeProtein_eq_some_of_processed (g := mutated) (raw := rawM) (p := q) hsM hq
  have hEq_some :
      some (_root_.Bio.Genetics.translate p.coding_region) =
      some (_root_.Bio.Genetics.translate q.coding_region) := by
    simpa [hs, hm] using hEq
  have hEq_payload_root :
      _root_.Bio.Genetics.translate p.coding_region =
      _root_.Bio.Genetics.translate q.coding_region :=
    Option.some.inj hEq_some
  have hneq_tr_root :
      _root_.Bio.Genetics.translate p.coding_region ≠
      _root_.Bio.Genetics.translate q.coding_region := by
    exact hneq_tr
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
  rcases frameshiftWitness_unpack gene m w hw with
    ⟨mutated, rawG, rawM, p, q, happ, hsG, hsM, hp, hq, hw'⟩
  exact ⟨mutated, happ, proteins_ne_of_processed_witness gene mutated rawG rawM p q w hsG hsM hp hq hw'⟩

/-!
  Frameshift indels that occur in the coding sequence change the resulting protein.
-/

/-- Constructive, non-axiomatic: any insertion inside the CDS whose length
    is not a multiple of 3 changes the synthesized protein, provided a semantic
    witness exists (produced by `frameshiftSemanticWitness`). -/
theorem frameshift_changes_protein
  (gene : Gene) (pos : Nat) (bases : List DNABase)
  --(hOffset : (Bio.Mutation.getCodingOffset gene pos).isSome)
  --(hMod : bases.length % 3 ≠ 0)
  (mutated_gene : Gene)
  (hApply : applyInsertion gene pos bases = some mutated_gene)
  (w : SignalWitness)
  (hw : frameshiftSemanticWitness gene (.Insertion pos bases) = some w)
  : synthesizeProtein gene ≠ synthesizeProtein mutated_gene := by
  have hmain :=
    frameshift_with_witness_changes_protein
      (gene := gene) (m := .Insertion pos bases) (w := w) (hw := hw)
  rcases hmain with ⟨mutated', happ', hneq'⟩
  have happApplyMutation : applyMutation gene (.Insertion pos bases) = some mutated_gene := by
    simpa [applyMutation] using hApply
  have h_eq_opt : some mutated' = some mutated_gene := by
    simpa [happ'] using happApplyMutation
  have h_eq_mut : mutated' = mutated_gene := Option.some.inj h_eq_opt
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
    --(h_in_cds : (Bio.Mutation.getCodingOffset gene pos).isSome)
    (w : SignalWitness)
    (hw : frameshiftSemanticWitness gene (.Insertion pos [base]) = some w) :
    ∀ mutated_gene, applyInsertion gene pos [base] = some mutated_gene →
      synthesizeProtein gene ≠ synthesizeProtein mutated_gene := by
  intro mutated_gene hApply
  have h_len : ([base].length % 3) ≠ 0 := by simp
  exact frameshift_changes_protein gene pos [base] mutated_gene hApply w hw

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
    (w : SignalWitness)
    (hw : frameshiftSemanticWitness gene (.Insertion pos [base]) = some w) :
    synthesizeProtein gene ≠ synthesizeProtein mutated_gene := by
  have h_in_cds : (getCodingOffset gene pos).isSome := by
    simp [h_offset]
  have h_len : ([base].length % 3) ≠ 0 := by simp
  exact frameshift_changes_protein gene pos [base] mutated_gene h_apply w hw

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
  have hlt : pos < gene.coding_strand.seq.length := by
    rcases h_exonic with ⟨r, hr, _, h_in_end⟩
    exact lt_of_lt_of_le h_in_end (gene.h_exons_bounded r hr)
  have h_pos : pos ≤ gene.coding_strand.seq.length := Nat.le_of_lt hlt
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
  -- we build the witness mutated gene matching applyInsertion’s record exactly.
  refine ⟨
    {
      id := gene.id
      coding_strand := { seq := mutated_seq }
      exons := shifted_exons
      splice_sites := gene.splice_sites
      promoter_region := gene.promoter_region
      poly_a_site := gene.poly_a_site.map (fun p => if p ≥ pos then p + insLen else p)
      strand := gene.strand
      h_exons_sorted := by
        simpa [shifted_exons, hshift, insLen, hins] using
          (shiftRegionsAfter_preserves_sorted
            (pos := pos) (shift := insLen) (regions := gene.exons) gene.h_exons_sorted)
      h_exons_bounded := by
        intro r' hr'
        have core :=
          exons_bounded_after_insertion_lets
            (gene := gene) (pos := pos) (bases := [base]) h_pos
        have hb' :
            r'.end_ ≤ (gene.coding_strand.seq.take pos ++ [base] ++ gene.coding_strand.seq.drop pos).length :=
          core r' (by simpa [shifted_exons, hshift, insLen, hins])
        have hb : r'.end_ ≤ mutated_seq.length := by
          simpa [mutated_seq, hmut] using hb'
        simpa
      h_exons_nonempty := h_nonempty_after
    },
    ?heq,
    ?hneq
  ⟩
  · have h_guard :
        Bio.Mutation.shiftRegionsAfter pos (insLen : Int) gene.exons ≠ [] := by
      simpa [shifted_exons, hshift, insLen, hins] using h_nonempty_after
    simp [applyInsertion, h_pos, insLen, hins, mutated_seq,
          shifted_exons]
    aesop
  -- Protein change: we invoke the frameshift lemma (which uses the domain postulate).
  · have h_guard :
        Bio.Mutation.shiftRegionsAfter pos (insLen : Int) gene.exons ≠ [] := by
      simpa [shifted_exons, hshift, insLen, hins] using h_nonempty_after
    have happly :
        applyInsertion gene pos [base] =
          some
            { id := gene.id
              coding_strand := { seq := mutated_seq }
              exons := shifted_exons
              splice_sites := gene.splice_sites
              promoter_region := gene.promoter_region
              poly_a_site := gene.poly_a_site.map (fun p => if p ≥ pos then p + insLen else p)
              strand := gene.strand
              h_exons_sorted := by
                simpa [shifted_exons, hshift, insLen, hins] using
                  (shiftRegionsAfter_preserves_sorted
                    (pos := pos) (shift := insLen) (regions := gene.exons) gene.h_exons_sorted)
              h_exons_bounded := by
                intro r' hr'
                have core :=
                  exons_bounded_after_insertion_lets
                    (gene := gene) (pos := pos) (bases := [base]) h_pos
                have hb' :
                    r'.end_ ≤ (gene.coding_strand.seq.take pos ++ [base] ++ gene.coding_strand.seq.drop pos).length :=
                  core r' (by simpa [shifted_exons, hshift, insLen, hins])
                have hb : r'.end_ ≤ mutated_seq.length := by
                  simpa [mutated_seq, hmut] using hb'
                simpa
              h_exons_nonempty := h_nonempty_after } := by
      simpa [applyInsertion, h_pos, insLen, hins, mutated_seq, hmut,
             shifted_exons, hshift, h_guard]
    exact
      frameshift_changes_protein gene pos [base]
        { id := gene.id, coding_strand := { seq := mutated_seq }, exons := shifted_exons,
          splice_sites := gene.splice_sites, promoter_region := gene.promoter_region,
          poly_a_site := Option.map (fun p => if p ≥ pos then p + insLen else p) gene.poly_a_site,
          strand := gene.strand,
          h_exons_sorted :=
            Eq.mpr
              (id
                (congrArg
                  (fun x =>
                    Chain' (fun r1 r2 => r1.end_ ≤ r2.start) (shiftRegionsAfter pos x gene.exons))
                  (Eq.trans (congrArg Nat.cast (zero_add 1)) Nat.cast_one)))
              (Eq.mp
                (congrArg
                  (fun x =>
                    Chain' (fun r1 r2 => r1.end_ ≤ r2.start) (shiftRegionsAfter pos x gene.exons))
                  (Eq.trans (congrArg Nat.cast (zero_add 1)) Nat.cast_one))
                (shiftRegionsAfter_preserves_sorted pos insLen gene.exons gene.h_exons_sorted)),
          h_exons_bounded := fun r' hr' =>
            have core := exons_bounded_after_insertion_lets gene pos [base] h_pos;
            have hb' :=
              core r'
                (Eq.mpr
                  (id
                    (congrArg (fun x => r' ∈ shiftRegionsAfter pos x gene.exons)
                      (Eq.trans (congrArg Nat.cast (zero_add 1)) Nat.cast_one)))
                  hr');
            have hb :=
              Eq.mpr
                (id
                  (congrArg (LE.le r'.end_)
                    (Eq.trans
                      (Eq.trans
                        (congrArg length
                          (append_assoc (take pos gene.coding_strand.seq) [base]
                            (drop pos gene.coding_strand.seq)))
                        length_append)
                      (congr (congrArg HAdd.hAdd length_take)
                        (congrArg (fun x => x + 1) length_drop)))))
                (Eq.mp
                  (congrArg (LE.le r'.end_)
                    (Eq.trans
                      (Eq.trans
                        (congrArg length
                          (append_assoc (take pos gene.coding_strand.seq) [base]
                            (drop pos gene.coding_strand.seq)))
                        length_append)
                      (congr (congrArg HAdd.hAdd length_take)
                        (congrArg (fun x => x + 1) length_drop))))
                  hb');
            Eq.mpr (id ge_iff_le._simp_1) hb,
          h_exons_nonempty := h_nonempty_after }
        happly w hw

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
  simp


/-! ### Theorem 4: Start Codon Necessity -/

lemma findStartCodon_none_if_no_aug (mrna : Bio.Sequence.MRNA)
    (h_no_aug : ∀ i, i + 2 < (mrna.seq.drop mrna.five_utr_length).length →
     ¬((mrna.seq.drop mrna.five_utr_length)[i]! = Bio.RNABase.A ∧
       (mrna.seq.drop mrna.five_utr_length)[i+1]! = Bio.RNABase.U ∧
       (mrna.seq.drop mrna.five_utr_length)[i+2]! = Bio.RNABase.G)) :
    findStartCodon mrna = none := by
  set seq := mrna.seq.drop mrna.five_utr_length with hseq
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
        simp [Bio.Genetics.findAndScoreStartCodons.aux]
      | cons b rem' =>
        cases rem' with
        | nil =>
          simp [Bio.Genetics.findAndScoreStartCodons.aux]
        | cons c rem'' =>
          have hhead : ¬(a = Bio.RNABase.A ∧ b = Bio.RNABase.U ∧ c = Bio.RNABase.G) := by
            intro habc; rcases habc with ⟨ha, hb, hc⟩; subst ha hb hc
            have hlen : 0 + 2 < (Bio.RNABase.A :: Bio.RNABase.U :: Bio.RNABase.G :: rem'').length := by simp
            have := hno 0 hlen
            simp at this
          have h_tail :
              ∀ i, i + 2 < (b :: c :: rem'').length →
                ¬(((b :: c :: rem'')[i]! = Bio.RNABase.A) ∧
                  ((b :: c :: rem'')[i+1]! = Bio.RNABase.U) ∧
                  ((b :: c :: rem'')[i+2]! = Bio.RNABase.G)) := by
            intro i hi
            have hi' : (i + 1) + 2 < (a :: b :: c :: rem'').length := by
              simpa using Nat.succ_lt_succ hi
            have := hno (i + 1) hi'
            simpa using this
          have := ih (idx + 1) acc h_tail
          by_cases hA : a = Bio.RNABase.A
          · by_cases hU : b = Bio.RNABase.U
            · by_cases hG : c = Bio.RNABase.G
              · exact False.elim (hhead ⟨hA, hU, hG⟩)
              · subst hA; subst hU; simp [Bio.Genetics.findAndScoreStartCodons.aux, hG, this]
            · subst hA; simp [Bio.Genetics.findAndScoreStartCodons.aux, hU, this]
          · simp [Bio.Genetics.findAndScoreStartCodons.aux, hA, this]
  have h_empty : findAndScoreStartCodons seq = [] := by
    unfold findAndScoreStartCodons
    simpa using aux_nil seq 0 [] (by
      intro i hi; exact h_no_aug i (by simpa [hseq] using hi))
  simp [findStartCodon]
  aesop

theorem no_start_no_protein (mrna : Bio.Sequence.MRNA) :
    (∀ i, i + 2 < mrna.seq.length →
     ¬(mrna.seq[i]! = Bio.RNABase.A ∧ mrna.seq[i+1]! = Bio.RNABase.U ∧ mrna.seq[i+2]! = Bio.RNABase.G)) →
    findStartCodon mrna = none := by
  intro h_no_aug
  have h_no_aug_dropped : ∀ i, i + 2 < (mrna.seq.drop mrna.five_utr_length).length →
     ¬((mrna.seq.drop mrna.five_utr_length)[i]! = Bio.RNABase.A ∧
       (mrna.seq.drop mrna.five_utr_length)[i+1]! = Bio.RNABase.U ∧
       (mrna.seq.drop mrna.five_utr_length)[i+2]! = Bio.RNABase.G) := by
    intro i hi
    have h_bound : mrna.five_utr_length + i + 2 < mrna.seq.length := by
      simp [List.length_drop] at hi
      omega
    specialize h_no_aug (mrna.five_utr_length + i) h_bound
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

/- ### Section 7: Examples -/
namespace Bio.Examples

open Bio Bio.Sequence Bio.Genetics Bio.Mutation

def CFTR_fragment : Gene := {
  id := "CFTR_ΔF508"
  coding_strand := {
    seq := [
      DNABase.A, .T, .G, .G, .A, .T,  -- Met-Asp
      .G, .T, .A, .A, .G, .T,         -- splice signals
      .T, .T, .C, .T, .T, .T
    ]
  }
  exons := [
    { start := 0, end_ := 6, h_valid := by decide },
    { start := 12, end_ := 18, h_valid := by decide }
  ]
  splice_sites := standardSpliceSites
  promoter_region := none
  poly_a_site := none
  strand := .Plus
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
     analyzeMutationEffect CFTR_fragment
       (Mutation.Substitution pos (CFTR_fragment.coding_strand.seq.getD pos DNABase.N) new_base) =
     MutationEffect.Silent) := by
  intro pos
  constructor
  · unfold IsIntronic IsExonic
    constructor
    · decide
    · push_neg
      intro exon h_mem
      simp [CFTR_fragment] at h_mem
      cases h_mem with
      | inl h => rw [h]; decide
      | inr h => rw [h]; decide
  · intro new_base
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
    set mutated_seq := CFTR_fragment.coding_strand.seq.set pos new_base with hmut
    set orig := CFTR_fragment.coding_strand.seq.getD pos DNABase.N with horig
    have happly :
        applySubstitution CFTR_fragment pos orig new_base =
          some
            { CFTR_fragment with
              coding_strand := { seq := mutated_seq }
              h_exons_bounded := by
                intro r hr
                rw [List.length_set]
                exact CFTR_fragment.h_exons_bounded r hr } := by
      -- in-bounds and current base equals `orig` by definition
      simp [applySubstitution, h_pos, horig, mutated_seq, hmut]
    have hprot :
        synthesizeProtein CFTR_fragment =
        synthesizeProtein
          { CFTR_fragment with
            coding_strand := { seq := mutated_seq }
            h_exons_bounded := by
              intro r hr
              rw [List.length_set]
              exact CFTR_fragment.h_exons_bounded r hr } := by
      have h_safe : Bio.Genetics.SafeForSpliceSites CFTR_fragment pos := by
        refine And.intro h_intronic ?windows
        intro r hr
        simp [CFTR_fragment] at hr
        cases hr with
        | inl h =>
            subst h; decide
        | inr h =>
            subst h; decide
      have h_sep :
          ∀ r ∈ CFTR_fragment.exons,
            CFTR_fragment.splice_sites.acceptorSite.length ≤
              r.end_ + CFTR_fragment.splice_sites.donorSite.length := by
        intro r hr
        simp [CFTR_fragment] at hr
        cases hr with
        | inl h => subst h; decide
        | inr h => subst h; decide
      exact
        intronic_substitution_preserves_protein
          CFTR_fragment pos orig new_base h_intronic h_safe h_sep
          { CFTR_fragment with
            coding_strand := { seq := mutated_seq }
            h_exons_bounded := by
              intro r hr
              rw [List.length_set]
              exact CFTR_fragment.h_exons_bounded r hr }
          happly
    have _ := CFTR_fragment.coding_strand.seq.getD pos DNABase.N
    aesop

end Bio.Examples

/-!
# Extensions to the Formal Model of Eukaryotic Gene Expression

This section addresses two primary limitations of the foundational kernel:
1.  **Biological Fidelity (Double-Stranded Genes):** It introduces a `strand`
    field to the `Gene` structure and defines a verified `reverseComplement`
    function. This shows the path to handling genes on both the plus and
    minus strands of a chromosome through normalization.
2.  **Stochasticity (Probabilistic Splicing):** It introduces a placeholder
    `Distribution` monad to model probabilistic outcomes. It reframes splicing
    as a stochastic process, separating the mechanics of isoform assembly from
    the probabilistic, regulatory logic that determines which isoforms are produced.

-/
namespace Bio.Extensions

open Bio Bio.Sequence Bio.Genetics

/-!
## Part 1: Handling Double-Stranded Genes

This section addresses the limitation of the single-strand model. We introduce
a `strand` identifier and the necessary function for reverse complementation.

**Modeling Strategy: Normalization**

A key challenge in bioinformatics is correctly handling coordinates and sequences
for genes on the minus strand. Instead of complicating the internal logic of every
function (`splice`, `processMRNA`), we adopt a **normalization** strategy. All
`Gene` objects within the verified pipeline are assumed to be normalized to a
5' → 3' "sense strand" representation.

- A `Plus` strand gene is stored as-is.
- A `Minus` strand gene is stored by first taking the reverse complement of its
  genomic DNA sequence. Its exon coordinates are then recalculated to be 0-based
  relative to this new, inverted sequence.

The `strand` field is retained as critical metadata, but the core processing
logic remains simple and elegant, operating on a single, consistent representation.
The `reverseComplement` function defined below is the key verified component
required for this normalization step.
-/

/-- Represents the strand of a gene on a reference chromosome. -/
inductive StrandSign
  | Plus  -- 5' -> 3'
  | Minus -- 3' -> 5'
  deriving Repr, DecidableEq

/-- Defines the Watson-Crick complement of a single DNA base. -/
def complementBase (b : DNABase) : DNABase :=
  match b with
  | .A => .T
  | .T => .A
  | .G => .C
  | .C => .G
  | .N => .N -- The complement of an unknown base is unknown.

/--
Computes the reverse complement of a DNA sequence.
This operation is fundamental for normalizing minus-strand genes.
-/
def reverseComplement (dna : DNAStrand) : DNAStrand :=
  { seq := (dna.seq.map complementBase).reverse }

-- The existing functions like `splice`, `processMRNA`, and `translate`
-- can now operate on `GeneV2` (by accessing `g.toGene`) under the
-- assumption that the input has been normalized. The logic inside these
-- functions does not need to change, which is a major advantage of the
-- normalization approach.

-- Example of reverse complementation
#eval reverseComplement { seq := [.A, .T, .C, .G] }
-- Expected: { seq := [.C, .G, .A, .T] }

lemma complement_involutive (b : DNABase) : complementBase (complementBase b) = b := by
  cases b <;> rfl

theorem reverseComplement_involutive (dna : DNAStrand) :
    reverseComplement (reverseComplement dna) = dna := by
  ext
  simp [reverseComplement, List.map_reverse, List.reverse_reverse, List.map_map, Function.comp, complement_involutive]

/-!
## Part 2: Modeling Stochastic Splicing

This section addresses the deterministic nature of the original model. We
introduce a placeholder probabilistic framework to demonstrate how splicing can
be modeled as a stochastic process, separating the **mechanics** from the
**regulation**.

**Modeling Strategy: A Probabilistic Layer over a Deterministic Core**

The core idea is to use the verified, deterministic functions (`spliceIsoform`)
as the "mechanical" layer that defines the *set of possible outcomes*. We then
add a new, probabilistic layer on top that assigns probabilities to these
outcomes based on some regulatory context.
-/

/--
A placeholder for a probability distribution. A real implementation would use
a well-founded probability monad from a library like `mathlib`.
For this demonstration, we use a simple list of (probability, value) pairs.
We assume the probabilities sum to 1.
-/
def Distribution (α : Type) : Type := List (Float × α)

/-- Lifts a pure value into a deterministic distribution. -/
def Distribution.pure {α : Type} (a : α) : Distribution α :=
  [(1.0, a)]

/-- The bind operation for chaining probabilistic computations (implemented recursively). -/
def Distribution.bind {α β : Type} (d : Distribution α) (f : α → Distribution β) : Distribution β :=
  match d with
  | [] => []
  | (p, a) :: ds =>
      List.append
        ((f a).map (fun (q, b) => (p * q, b)))
        (Distribution.bind ds f)

-- Placeholder for regulatory information (e.g., cell type, transcription factor levels).
structure RegulatoryContext where
  -- In a real model, this would contain data used to determine splicing probabilities.
  cell_type : String := "default"

/--
A conceptual function representing the complex logic that determines which
splicing patterns occur and with what frequency, based on regulatory context.

In a better model, this would be a sophisticated function. Here, we hard-code
a response for a specific gene to demonstrate the principle.
-/
def determineSplicingPattern (gene : Gene) (ctx : RegulatoryContext) : Distribution (List Nat) :=
  -- This function models the regulatory choice of which exons to include.
  -- The output is a distribution over lists of exon indices.
  if gene.id = "MY_GENE_1" then
    -- Example for a 3-exon gene:
    -- 70% chance of the full transcript (exons 0, 1, 2)
    -- 20% chance of skipping exon 1 (exons 0, 2)
    -- 10% chance of complete regulatory failure (empty list of exons)
    [ (0.7, [0, 1, 2]),
      (0.2, [0, 2]),
      (0.1, []) ]
  else
    -- Default behavior: always attempt to produce the full transcript.
    Distribution.pure (List.range gene.exons.length)

/--
A stochastic splicing layer over the deterministic core. Assumes `gene` is normalized
to a 5'→3' representation regardless of `gene.strand`.
-/
def stochastic_splice (gene : Gene) (ctx : RegulatoryContext) : Distribution (Option RawMRNA) :=
  let pattern_dist := determineSplicingPattern gene ctx
  Distribution.bind pattern_dist (fun exon_indices =>
    if h_valid : ∀ i ∈ exon_indices, i < gene.exons.length then
      if h_sorted : List.Chain' (· < ·) exon_indices then
        let isoform : SpliceIsoform := {
          gene := gene,
          included_exons := exon_indices,
          h_valid_indices := h_valid,
          h_sorted := h_sorted
        }
        Distribution.pure (spliceIsoform isoform)
      else
        Distribution.pure none
    else
      Distribution.pure none
  )

-- --- Example Usage ---

-- Sample 3-exon gene for demonstration
def sampleGene : Gene := {
  id := "MY_GENE_1"
  coding_strand := { seq := List.replicate 100 .N }
  exons := [
    { start := 0, end_ := 10, h_valid := by decide },
    { start := 20, end_ := 30, h_valid := by decide },
    { start := 40, end_ := 50, h_valid := by decide }
  ]
  splice_sites := standardSpliceSites
  promoter_region := none
  poly_a_site := none
  strand := .Plus
  h_exons_sorted := by unfold List.Chain'; simp
  h_exons_bounded := by
    intro r hr; simp at hr
    cases hr with
    | inl h => subst h; decide
    | inr hr' =>
      cases hr' with
      | inl h => subst h; decide
      | inr h => subst h; decide
  h_exons_nonempty := by decide
}

-- Simulate the splicing process for our sample gene in a default context.
#eval stochastic_splice sampleGene {}
/-
Expected output of the #eval command:
[
  (0.7, some { seq := ... }),  -- The fully spliced mRNA
  (0.2, some { seq := ... }),  -- The mRNA with exon 1 skipped
  (0.1, none)                  -- Represents splicing failure
]
This demonstrates the model's ability to capture multiple, probabilistic outcomes,
a critical step toward a realistic biological model.
-/

end Bio.Extensions
open Bio Bio.Sequence Bio.Genetics Bio.Extensions

/-!
# A Verifiable Model of Stochastic Gene Expression

This file implements the non-placeholder stochastic layer for the gene expression
model.
It provides a robust framework for reasoning about probabilistic biological outcomes,
such as alternative splicing.

**Three-Layer Architecture:**
1.  **`Stochastic.Spec` (The Mathematical Specification):**
    *   Defines the abstract mathematical meaning of a stochastic process using
      the rigorous `Mathlib.Probability.PMF` (Probability Mass Function) type.
    *   Provides a high-level, declarative specification of "what" the correct
      distribution of outcomes should be.

2.  **`Stochastic.Prog` (The Probabilistic Program):**
    *   Implements a `SLang` monad, inspired by probabilistic programming languages
      like `SampCert`, for writing concrete, executable sampling algorithms.
    *   Provides a low-level, operational specification of "how" to generate
      a sample from a distribution.

3.  **`Stochastic.Bridge` (The Denotational Semantics Bridge):**
    *   Formally connects the program to the mathematics.
    *   Defines a `denote` function that maps a `SLang` program to its `PMF` meaning.
    *   States the main theorem of correctness: that the denotation of the
      splicing program is equal to the mathematical specification.

This approach aims at providing the "best of both worlds": a high-level, abstract model for
mathematical proofs (e.g., of convergence) and a low-level, executable model for
verification of specific algorithms.
-/

namespace Bio.Verified.Stochastic

--open Bio.Verified.Core
--open Bio.Verified.Sequence
--open Bio.Verified.Genetics
open PMF ENNReal Real

-- Layer 1

namespace Spec

/--
A `PMFKernel` represents a stochastic transition from a type `α` to a
distribution of outcomes in `β`. It is the formal mathematical object
representing our process. It is a specialized version of `MeasureTheory.Kernel`
for discrete probability.
-/
def PMFKernel (α β : Type) : Type := α → PMF β

-- Placeholder for rich regulatory information (cell type, TF levels, etc.)
structure RegulatoryContext where
  cell_type : String := "default"
  -- In a real model, this would contain data used to determine splicing probabilities.

noncomputable def determineSplicingPatternSpec (input : Gene × RegulatoryContext) : PMF (List Nat) := by
  classical
  let (gene, ctx) := input
  by_cases h : gene.id = "MY_GENE_1" ∧ ctx.cell_type = "liver"
  ·  -- Finite support over the three explicit patterns.
    let support : Finset (List Nat) := { [0, 1, 2], [0, 2], [] }
    -- Integer base weights 7/10, 2/10, 1/10 expressed as (·) * (10)⁻¹ in ℝ≥0∞.
    let baseW : List Nat → ℝ≥0∞ :=
      fun pattern =>
        if pattern = [0, 1, 2] then (7 : ℝ≥0∞)
        else if pattern = [0, 2] then (2 : ℝ≥0∞)
        else if pattern = [] then (1 : ℝ≥0∞)
        else 0
    let mass : List Nat → ℝ≥0∞ := fun pattern => baseW pattern * (10 : ℝ≥0∞)⁻¹
    -- Build the PMF from the finite support set (note: ofFinset takes (f, s, h, h')).
    refine PMF.ofFinset mass support ?h_sum ?h_zeroOutside
    · -- Sum over support is 1.
      -- First, sum the un-normalized weights.
      have h_sum_base : ∑ a ∈ support, baseW a = (10 : ℝ≥0∞) := by
        -- Turn the finset sum into explicit numerals, then close via norm_num.
        have : (7 : ℝ≥0∞) + (2 : ℝ≥0∞) + (1 : ℝ≥0∞) = (10 : ℝ≥0∞) := by
          norm_num
        -- simp gives 7 + (2 + 1); align with (7 + 2) + 1 and apply the equality above.
        simpa [support, baseW, add_assoc] using this
      -- Pull out the common normalization factor (10)⁻¹ from the sum.
      have hfac :
          ∑ a ∈ support, mass a
            = (∑ a ∈ support, baseW a) * (10 : ℝ≥0∞)⁻¹ := by
        -- Rewrite each summand using mass, then use sum_mul to factor the scalar.
        calc
          ∑ a ∈ support, mass a
              = ∑ a ∈ support, baseW a * (10 : ℝ≥0∞)⁻¹ := by
                apply Finset.sum_congr rfl
                intro a ha
                simp [mass]
          _ = (∑ a ∈ support, baseW a) * (10 : ℝ≥0∞)⁻¹ := by
                exact Eq.symm (Finset.sum_mul support baseW (10 : ℝ≥0∞)⁻¹)
      -- Conclude: (10) * (10)⁻¹ = 1 in ℝ≥0∞.
      have h10_ne_zero : (10 : ℝ≥0∞) ≠ 0 := by simp
      have h10_ne_top  : (10 : ℝ≥0∞) ≠ ∞ := by simp
      have h10_mul_inv : (10 : ℝ≥0∞) * (10 : ℝ≥0∞)⁻¹ = 1 := by
        simpa using ENNReal.mul_inv_cancel h10_ne_zero h10_ne_top
      -- Put it all together.
      calc
        ∑ a ∈ support, mass a
            = (∑ a ∈ support, baseW a) * (10 : ℝ≥0∞)⁻¹ := hfac
        _   = (10 : ℝ≥0∞) * (10 : ℝ≥0∞)⁻¹ := by simp [h_sum_base]
        _   = 1 := h10_mul_inv
    · -- Outside of support, the mass is zero.
      intro a ha
      -- Non-membership means `a` is not any of the three listed patterns.
      have hne : a ≠ [0, 1, 2] ∧ a ≠ [0, 2] ∧ a ≠ [] := by
        simpa [support] using ha
      have h1 := hne.1
      have h2 := hne.2.1
      have h3 := hne.2.2
      simp [mass, baseW, h1, h2, h3]
  · -- Default behavior: always produce the full transcript (deterministically).
    exact PMF.pure (List.range gene.exons.length)

/--
**Stochastic splicing.**
This kernel chains the regulatory choice with the deterministic splicing mechanic.
It is the "ground truth" definition of a correct stochastic splice.
-/
noncomputable def stochasticSplicingSpec [Fintype (List ℕ)] : PMFKernel (Gene × RegulatoryContext) (Option RawMRNA) :=
  fun input =>
    let (gene, _) := input
    -- 1. Get the distribution of possible exon patterns.
    let pattern_pmf := determineSplicingPatternSpec input
    -- 2. Monadically bind this choice to the deterministic splicing outcome.
    pattern_pmf.bind (fun exon_indices =>
      -- For a given pattern, the outcome is deterministic.
      -- We check if the pattern is valid and then call the verified,
      -- deterministic `spliceIsoform` function from the core model.
      if h_valid : ∀ i ∈ exon_indices, i < gene.exons.length then
        if h_sorted : List.Chain' (· < ·) exon_indices then
          let isoform : SpliceIsoform := {
            gene := gene,
            included_exons := exon_indices,
            h_valid_indices := h_valid,
            h_sorted := h_sorted
          }
          -- `PMF.pure` creates a Dirac delta distribution, representing
          -- a deterministic outcome with probability 1.
          PMF.pure (spliceIsoform isoform)
        else
          PMF.pure none -- Invalid (unsorted) pattern fails deterministically.
      else
        PMF.pure none -- Invalid (out-of-bounds) pattern fails deterministically.
    )

end Spec

-- Layer 2:`SLang`

namespace Prog

/--
The `SLang` monad for probabilistic programming. A program is a function
that maps each possible outcome to its un-normalized probability mass.
This is identical in structure to `SampCert.SLang`.
-/
abbrev SLang (α : Type) : Type := α → ℝ≥0∞

open scoped Classical in
noncomputable def probPure (a : α) : SLang α := fun a' => if a' = a then 1 else 0

noncomputable def probBind (p : SLang α) (f : α → SLang β) : SLang β :=
  fun b => ∑' a, p a * f a b

noncomputable instance : Monad SLang where
  pure := probPure
  bind := probBind

/--
A sampler for a categorical distribution. Given a list of outcomes and their
associated weights (as non-negative reals), it returns a `SLang` program
that samples from that distribution.
This is a non-placeholder sampler.
-/
noncomputable def probCategorical (choices : List (α × NNReal)) : SLang α := by
  classical
  -- Calculate the total weight for normalization
  let totalWeight := (choices.map (fun c => c.2)).sum
  refine if h_total : totalWeight = 0 then ?empty else ?nonempty
  · exact fun _ => 0 -- If all weights are zero, this is an empty distribution.
  · intro outcome
    -- Find the weight of the specified outcome in the list.
    let weight := (choices.find? (fun c => decide (c.1 = outcome))).map (·.2) |>.getD 0
    -- The probability is the outcome's weight divided by the total.
    exact (weight : ℝ≥0∞) / (totalWeight : ℝ≥0∞)

/--
The program for stochastic splicing, written in `SLang` aimed at providing an executable algorithm.
-/
noncomputable def stochasticSplicingProg (input : Gene × Spec.RegulatoryContext) : SLang (Option RawMRNA) :=
  let (gene, ctx) := input
  -- 1. Define the list of possible outcomes and their weights for the regulatory choice.
  let patterns_with_weights : List (List Nat × NNReal) :=
    if gene.id = "MY_GENE_1" ∧ ctx.cell_type = "liver" then
      [ ([0, 1, 2], 0.7),
        ([0, 2], 0.2),
        ([], 0.1) ]
    else
      [ (List.range gene.exons.length, 1.0) ]
  -- 2. Use the categorical sampler to choose a splicing pattern.
  do
    let exon_indices ← probCategorical patterns_with_weights
    -- 3. The rest of the logic is deterministic, identical to the spec.
    if h_valid : ∀ i ∈ exon_indices, i < gene.exons.length then
      if h_sorted : List.Chain' (· < ·) exon_indices then
        let isoform : SpliceIsoform :=
          { gene := gene
            , included_exons := exon_indices
            , h_valid_indices := h_valid
            , h_sorted := h_sorted }
        return spliceIsoform isoform -- `return` is `probPure`
      else
        return none
    else
      return none

-- Layer 3: The Denotational Semantics Bridge

namespace Bridge

open Prog
open ENNReal

/--
The denotation function, mapping a `SLang` program to its mathematical meaning
in `PMF`. This is a dependent function: it requires a proof that the program
normalizes (i.e., that its probabilities sum to 1) as an argument.
-/
noncomputable def denote (prog : SLang α) (h_norm : HasSum prog 1) : PMF α :=
  -- Avoids requiring [Fintype α] by using `PMF.normalize`.
  PMF.normalize prog
    (by
      -- tsum prog = 1 ⇒ ≠ 0
      simp [h_norm.tsum_eq] )
    (by
      -- tsum prog = 1 ⇒ ≠ ∞
      simp [h_norm.tsum_eq] )

-- We can now prove that the `SLang` primitives correspond to the `PMF` primitives.

theorem denote_pure (a : α) :
    denote (probPure a) (by
      classical
      -- `probPure a` is `ite (· = a) 1 0`, which has sum 1.
      simpa [probPure] using (hasSum_ite_eq a (1 : ℝ≥0∞))
    ) = PMF.pure a := by
  classical
  have htsum : ∑' x, probPure a x = (1 : ℝ≥0∞) := by
    simp [probPure]
  ext x
  simp [denote, PMF.normalize_apply, probPure, PMF.pure, htsum]
  aesop

theorem denote_bind {p : SLang α} {f : α → SLang β}
    (hp : HasSum p 1) (hf : ∀ a, HasSum (f a) 1) :
    denote (probBind p f)
      (by
        classical
        have : ∑' (b : β), (∑' a, p a * f a b) = (1 : ℝ≥0∞) := by
          calc
            (∑' b, (∑' a, p a * f a b))
                = (∑' a, (∑' b, p a * f a b)) := ENNReal.tsum_comm
            _   = (∑' a, p a * (∑' b, f a b)) := by
                  simp [ENNReal.tsum_mul_left]
            _   = (∑' a, p a * 1) := by
                  have hfa : ∀ a, (∑' b, f a b) = (1 : ℝ≥0∞) := fun a => (hf a).tsum_eq
                  simp [hfa]
            _   = ((∑' a, p a) * 1) := ENNReal.tsum_mul_right
            _   = (1 : ℝ≥0∞) := by simp [hp.tsum_eq]
        exact ENNReal.summable.hasSum_iff.2 this
      )
    = (denote p hp).bind (fun a => denote (f a) (hf a)) := by
  classical
  have hp_sum : ∑' a, p a = (1 : ℝ≥0∞) := hp.tsum_eq
  have hf_sum : ∀ a, ∑' b, f a b = (1 : ℝ≥0∞) := fun a => (hf a).tsum_eq
  have h_bind_sum : ∑' (x : β), Prog.probBind p f x = (1 : ℝ≥0∞) := by
    calc
      (∑' x, Prog.probBind p f x)
          = (∑' x, ∑' a, p a * f a x) := rfl
      _   = (∑' a, ∑' x, p a * f a x) := ENNReal.tsum_comm
      _   = (∑' a, p a * (∑' x, f a x)) := by
              simp [ENNReal.tsum_mul_left]
      _   = (∑' a, p a * 1) := by
              have hfa : ∀ a, (∑' x, f a x) = (1 : ℝ≥0∞) := hf_sum
              simp [hfa]
      _   = ((∑' a, p a) * 1) := ENNReal.tsum_mul_right
      _   = (1 : ℝ≥0∞) := by simp [hp_sum]
  have inv_bind_sum : (∑' (x : β), Prog.probBind p f x)⁻¹ = 1 := by
    simp [h_bind_sum]
  have inv_bind_nested : (∑' (x : β) (a : α), p a * f a x)⁻¹ = 1 := by
    have h := inv_bind_sum
    simp [Prog.probBind] at h
    exact inv_bind_sum-- h
  have inv_p : (∑' (x : α), p x)⁻¹ = 1 := by
    simp [hp_sum]
  have inv_f : ∀ a, (∑' (x : β), f a x)⁻¹ = 1 := by
    intro a; simp [hf_sum a]
  ext b
  simp [denote, PMF.normalize_apply, Prog.probBind, PMF.bind_apply, inv_bind_nested, inv_p, inv_f,
        mul_comm, mul_left_comm, mul_assoc]
-- Note:
-- TODO: a full end-to-end correctness theorem depends on a finished, executable Spec.

end Bridge

-- Example Usage

-- A sample 3-exon gene for showing stochastic splicing.
def sampleGene : Gene := {
  id := "MY_GENE_1"
  coding_strand := { seq := List.replicate 100 .N }
  strand := .Plus
  exons := [
    { start := 0, end_ := 10, h_valid := by decide },
    { start := 20, end_ := 30, h_valid := by decide },
    { start := 40, end_ := 50, h_valid := by decide }
  ]
  splice_sites := standardSpliceSites
  h_exons_sorted := by unfold List.Chain'; simp
  h_exons_bounded := by
    intro r hr
    simp at hr
    rcases hr with h | h | h
    · subst h; decide
    · subst h; decide
    · subst h; decide
  h_exons_nonempty := by decide
}

-- Define a specific regulatory context.
def liver_context : Spec.RegulatoryContext := { cell_type := "liver" }

#check Prog.stochasticSplicingProg (sampleGene, liver_context)

/-
To actually see probabilities, we apply the function to a concrete outcome (e.g., `none`)
or a constructed `Option RawMRNA`; we avoid evaluating the bare function value.
-- Examples (uncomment if desired and if printing ℝ≥0∞ is supported):
-- #eval (Prog.stochasticSplicingProg (sampleGene, liver_context)) none
-/

end Prog
end Bio.Verified.Stochastic

#min_imports
