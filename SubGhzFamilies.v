From Stdlib Require Import List Bool Arith Lia.

Import ListNotations.

Require Import SubGhzCore.

Definition CanonicalRFObject := list PulseClass.

Definition canonical_rf_object_from_runs (rs : Runs) : CanonicalRFObject :=
  canonical_normalized_pulse_classes rs.

Definition CoarseCanonicalRFObject := list CoarsePulseClass.

Definition coarse_canonical_rf_object_from_runs (rs : Runs) : CoarseCanonicalRFObject :=
  coarse_pulse_classes (canonical_rf_object_from_runs rs).

Definition tx_family_member (base_pattern : Runs) (te : nat) : Runs :=
  scale_runs te base_pattern.

Definition tx_family_object (base_pattern : Runs) : CanonicalRFObject :=
  canonical_rf_object_from_runs base_pattern.

Record FamilyDescriptor := {
  family_object : CanonicalRFObject;
  family_frame_bits : list bool
}.

Record FamilySemanticTower := {
  tower_object : CanonicalRFObject;
  tower_bits : list bool;
  tower_word : nat;
  tower_packet24 : Packet24;
  tower_fields : Packet24FieldView
}.

Definition family_descriptor_from_runs (rs : Runs) : FamilyDescriptor :=
  {| family_object := canonical_rf_object_from_runs rs;
     family_frame_bits := canonical_frame_bits_from_runs rs |}.

Definition tx_family_descriptor (base_pattern : Runs) : FamilyDescriptor :=
  family_descriptor_from_runs base_pattern.

Definition semantic_tower_from_runs (rs : Runs) : FamilySemanticTower :=
  {| tower_object := canonical_rf_object_from_runs rs;
     tower_bits := canonical_frame_bits_from_runs rs;
     tower_word := canonical_frame_word_from_runs rs;
     tower_packet24 := canonical_packet24_from_runs rs;
     tower_fields := canonical_packet24_field_view_from_runs rs |}.

Definition tx_family_semantic_tower (base_pattern : Runs) : FamilySemanticTower :=
  semantic_tower_from_runs base_pattern.

Theorem tx_family_canonical_object_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    canonical_rf_object_from_runs (tx_family_member base_pattern te) =
      tx_family_object base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold canonical_rf_object_from_runs, tx_family_member, tx_family_object.
  apply canonical_normalized_pulse_classes_scale_invariant.
  - exact Hte.
  - exact Hactive.
Qed.

Theorem tx_family_frame_bits_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    canonical_frame_bits_from_runs (tx_family_member base_pattern te) =
      canonical_frame_bits_from_runs base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold tx_family_member.
  apply canonical_frame_bits_from_runs_scale_invariant.
  - exact Hte.
  - exact Hactive.
Qed.

Theorem tx_family_frame_word_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    canonical_frame_word_from_runs (tx_family_member base_pattern te) =
      canonical_frame_word_from_runs base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold tx_family_member.
  apply canonical_frame_word_from_runs_scale_invariant.
  - exact Hte.
  - exact Hactive.
Qed.

Theorem tx_family_descriptor_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    family_descriptor_from_runs (tx_family_member base_pattern te) =
      tx_family_descriptor base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold family_descriptor_from_runs, tx_family_descriptor.
  rewrite tx_family_canonical_object_law by exact Hte || exact Hactive.
  rewrite tx_family_frame_bits_law by exact Hte || exact Hactive.
  reflexivity.
Qed.

Theorem tx_family_packet24_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    canonical_packet24_from_runs (tx_family_member base_pattern te) =
      canonical_packet24_from_runs base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold tx_family_member.
  apply canonical_packet24_from_runs_scale_invariant.
  - exact Hte.
  - exact Hactive.
Qed.

Theorem tx_family_field_view_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    canonical_packet24_field_view_from_runs (tx_family_member base_pattern te) =
      canonical_packet24_field_view_from_runs base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold tx_family_member.
  apply canonical_packet24_field_view_from_runs_scale_invariant.
  - exact Hte.
  - exact Hactive.
Qed.

Theorem tx_family_packet_structure_law :
  forall spec base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    canonical_packet_structure_view_from_runs spec (tx_family_member base_pattern te) =
      canonical_packet_structure_view_from_runs spec base_pattern.
Proof.
  intros spec base_pattern te Hte Hactive.
  unfold tx_family_member.
  apply canonical_packet_structure_view_from_runs_scale_invariant.
  - exact Hte.
  - exact Hactive.
Qed.

Theorem tx_family_counter_view_law :
  forall schema base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    canonical_field_counter_view_from_runs schema (tx_family_member base_pattern te) =
      canonical_field_counter_view_from_runs schema base_pattern.
Proof.
  intros schema base_pattern te Hte Hactive.
  unfold tx_family_member.
  apply canonical_field_counter_view_from_runs_scale_invariant.
  - exact Hte.
  - exact Hactive.
Qed.

Theorem tx_family_semantic_tower_law :
  forall base_pattern te,
    0 < te ->
    active_run_lengths base_pattern <> [] ->
    semantic_tower_from_runs (tx_family_member base_pattern te) =
      tx_family_semantic_tower base_pattern.
Proof.
  intros base_pattern te Hte Hactive.
  unfold semantic_tower_from_runs, tx_family_semantic_tower.
  rewrite tx_family_canonical_object_law by exact Hte || exact Hactive.
  rewrite tx_family_frame_bits_law by exact Hte || exact Hactive.
  rewrite tx_family_frame_word_law by exact Hte || exact Hactive.
  rewrite tx_family_packet24_law by exact Hte || exact Hactive.
  rewrite tx_family_field_view_law by exact Hte || exact Hactive.
  reflexivity.
Qed.

Corollary tx_family_members_share_canonical_object :
  forall base_pattern te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern <> [] ->
    canonical_rf_object_from_runs (tx_family_member base_pattern te1) =
      canonical_rf_object_from_runs (tx_family_member base_pattern te2).
Proof.
  intros base_pattern te1 te2 Hte1 Hte2 Hactive.
  unfold canonical_rf_object_from_runs, tx_family_member.
  apply canonical_normalized_pulse_classes_pairwise_scale_equal.
  - exact Hte1.
  - exact Hte2.
  - exact Hactive.
Qed.

Corollary tx_family_members_share_packet24 :
  forall base_pattern te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern <> [] ->
    canonical_packet24_from_runs (tx_family_member base_pattern te1) =
      canonical_packet24_from_runs (tx_family_member base_pattern te2).
Proof.
  intros base_pattern te1 te2 Hte1 Hte2 Hactive.
  transitivity (canonical_packet24_from_runs base_pattern).
  - apply tx_family_packet24_law.
    + exact Hte1.
    + exact Hactive.
  - symmetry.
    apply tx_family_packet24_law.
    + exact Hte2.
    + exact Hactive.
Qed.

Corollary tx_family_members_share_field_view :
  forall base_pattern te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern <> [] ->
    canonical_packet24_field_view_from_runs (tx_family_member base_pattern te1) =
      canonical_packet24_field_view_from_runs (tx_family_member base_pattern te2).
Proof.
  intros base_pattern te1 te2 Hte1 Hte2 Hactive.
  transitivity (canonical_packet24_field_view_from_runs base_pattern).
  - apply tx_family_field_view_law.
    + exact Hte1.
    + exact Hactive.
  - symmetry.
    apply tx_family_field_view_law.
    + exact Hte2.
    + exact Hactive.
Qed.

Corollary tx_family_members_share_packet_structure :
  forall spec base_pattern te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern <> [] ->
    canonical_packet_structure_view_from_runs spec (tx_family_member base_pattern te1) =
      canonical_packet_structure_view_from_runs spec (tx_family_member base_pattern te2).
Proof.
  intros spec base_pattern te1 te2 Hte1 Hte2 Hactive.
  transitivity (canonical_packet_structure_view_from_runs spec base_pattern).
  - apply tx_family_packet_structure_law.
    + exact Hte1.
    + exact Hactive.
  - symmetry.
    apply tx_family_packet_structure_law.
    + exact Hte2.
    + exact Hactive.
Qed.

Corollary tx_family_members_share_counter_view :
  forall schema base_pattern te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern <> [] ->
    canonical_field_counter_view_from_runs schema (tx_family_member base_pattern te1) =
      canonical_field_counter_view_from_runs schema (tx_family_member base_pattern te2).
Proof.
  intros schema base_pattern te1 te2 Hte1 Hte2 Hactive.
  transitivity (canonical_field_counter_view_from_runs schema base_pattern).
  - apply tx_family_counter_view_law.
    + exact Hte1.
    + exact Hactive.
  - symmetry.
    apply tx_family_counter_view_law.
    + exact Hte2.
    + exact Hactive.
Qed.

Theorem tx_family_object_and_base_order_law :
  forall base_pattern te1 te2,
    0 < te1 ->
    te1 < te2 ->
    runs_positive base_pattern = true ->
    active_run_lengths base_pattern <> [] ->
    canonical_rf_object_from_runs (tx_family_member base_pattern te1) =
      canonical_rf_object_from_runs (tx_family_member base_pattern te2) /\
    canonical_pulse_base_from_runs (tx_family_member base_pattern te1) <
      canonical_pulse_base_from_runs (tx_family_member base_pattern te2).
Proof.
  intros base_pattern te1 te2 Hte1 Hlt Hpos Hactive.
  unfold canonical_rf_object_from_runs, tx_family_member.
  apply canonical_normalized_pulse_classes_equal_but_bases_ordered.
  - exact Hte1.
  - exact Hlt.
  - exact Hpos.
  - exact Hactive.
Qed.

Theorem tx_families_with_distinct_objects_stay_separated :
  forall base_pattern1 base_pattern2 te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern1 <> [] ->
    active_run_lengths base_pattern2 <> [] ->
    tx_family_object base_pattern1 <> tx_family_object base_pattern2 ->
    canonical_rf_object_from_runs (tx_family_member base_pattern1 te1) <>
      canonical_rf_object_from_runs (tx_family_member base_pattern2 te2).
Proof.
  intros base_pattern1 base_pattern2 te1 te2 Hte1 Hte2 Hactive1 Hactive2 Hneq.
  unfold tx_family_object, canonical_rf_object_from_runs, tx_family_member in *.
  apply canonical_normalized_pulse_classes_scale_separated.
  - exact Hte1.
  - exact Hte2.
  - exact Hactive1.
  - exact Hactive2.
  - exact Hneq.
Qed.

Fixpoint strictly_increasing (xs : list nat) : Prop :=
  match xs with
  | [] => True
  | x :: xs' =>
      match xs' with
      | [] => True
      | y :: _ => x < y /\ strictly_increasing xs'
      end
  end.

Definition predicted_tx_family_objects
    (base_pattern : Runs)
    (tes : list nat)
    : list CanonicalRFObject :=
  map (fun te => canonical_rf_object_from_runs (tx_family_member base_pattern te)) tes.

Definition predicted_tx_family_bases
    (base_pattern : Runs)
    (tes : list nat)
    : list nat :=
  map (fun te => canonical_pulse_base_from_runs (tx_family_member base_pattern te)) tes.

Definition predicted_tx_family_frame_words
    (base_pattern : Runs)
    (tes : list nat)
    : list nat :=
  map (fun te => canonical_frame_word_from_runs (tx_family_member base_pattern te)) tes.

Definition predicted_tx_family_packets
    (base_pattern : Runs)
    (tes : list nat)
    : list Packet24 :=
  map (fun te => canonical_packet24_from_runs (tx_family_member base_pattern te)) tes.

Definition predicted_tx_family_field_views
    (base_pattern : Runs)
    (tes : list nat)
    : list Packet24FieldView :=
  map (fun te => canonical_packet24_field_view_from_runs (tx_family_member base_pattern te)) tes.

Definition predicted_tx_family_packet_structures
    (spec : PacketStructureSpec)
    (base_pattern : Runs)
    (tes : list nat)
    : list (list PacketStructuredFieldValue) :=
  map (fun te => canonical_packet_structure_view_from_runs spec (tx_family_member base_pattern te)) tes.

Definition predicted_tx_family_counter_views
    (schema : CounterSchema)
    (base_pattern : Runs)
    (tes : list nat)
    : list FieldCounterView :=
  map (fun te => canonical_field_counter_view_from_runs schema (tx_family_member base_pattern te)) tes.

Definition predicted_tx_family_towers
    (base_pattern : Runs)
    (tes : list nat)
    : list FamilySemanticTower :=
  map (fun te => semantic_tower_from_runs (tx_family_member base_pattern te)) tes.

Record TxSweepPrediction := {
  sweep_prediction_object : CanonicalRFObject;
  sweep_prediction_bases : list nat
}.

Record TxSweepSemanticPrediction := {
  semantic_prediction_object : CanonicalRFObject;
  semantic_prediction_bits : list bool;
  semantic_prediction_word : nat;
  semantic_prediction_packet24 : Packet24;
  semantic_prediction_fields : Packet24FieldView;
  semantic_prediction_bases : list nat
}.

Definition tx_family_sweep_prediction
    (base_pattern : Runs)
    (tes : list nat)
    : TxSweepPrediction :=
  {| sweep_prediction_object := tx_family_object base_pattern;
     sweep_prediction_bases := predicted_tx_family_bases base_pattern tes |}.

Definition tx_family_semantic_prediction
    (base_pattern : Runs)
    (tes : list nat)
    : TxSweepSemanticPrediction :=
  {| semantic_prediction_object := tx_family_object base_pattern;
     semantic_prediction_bits := canonical_frame_bits_from_runs base_pattern;
     semantic_prediction_word := canonical_frame_word_from_runs base_pattern;
     semantic_prediction_packet24 := canonical_packet24_from_runs base_pattern;
     semantic_prediction_fields := canonical_packet24_field_view_from_runs base_pattern;
     semantic_prediction_bases := predicted_tx_family_bases base_pattern tes |}.

Theorem predicted_tx_family_objects_constant :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_objects base_pattern tes =
      repeat (tx_family_object base_pattern) (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  induction Htes as [|te tes Hte Htes IH]; simpl.
  - reflexivity.
  - rewrite (tx_family_canonical_object_law base_pattern te Hte Hactive).
    rewrite IH.
    reflexivity.
Qed.

Theorem predicted_tx_family_frame_words_constant :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_frame_words base_pattern tes =
      repeat (canonical_frame_word_from_runs base_pattern) (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  induction Htes as [|te tes Hte Htes IH]; simpl.
  - reflexivity.
  - rewrite (tx_family_frame_word_law base_pattern te Hte Hactive).
    rewrite IH.
    reflexivity.
Qed.

Theorem predicted_tx_family_packets_constant :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_packets base_pattern tes =
      repeat (canonical_packet24_from_runs base_pattern) (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  induction Htes as [|te tes Hte Htes IH]; simpl.
  - reflexivity.
  - rewrite (tx_family_packet24_law base_pattern te Hte Hactive).
    rewrite IH.
    reflexivity.
Qed.

Theorem predicted_tx_family_field_views_constant :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_field_views base_pattern tes =
      repeat (canonical_packet24_field_view_from_runs base_pattern) (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  induction Htes as [|te tes Hte Htes IH]; simpl.
  - reflexivity.
  - rewrite (tx_family_field_view_law base_pattern te Hte Hactive).
    rewrite IH.
    reflexivity.
Qed.

Theorem predicted_tx_family_packet_structures_constant :
  forall spec base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_packet_structures spec base_pattern tes =
      repeat (canonical_packet_structure_view_from_runs spec base_pattern) (length tes).
Proof.
  intros spec base_pattern tes Htes Hactive.
  induction Htes as [|te tes Hte Htes IH]; simpl.
  - reflexivity.
  - rewrite (tx_family_packet_structure_law spec base_pattern te Hte Hactive).
    rewrite IH.
    reflexivity.
Qed.

Theorem predicted_tx_family_counter_views_constant :
  forall schema base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_counter_views schema base_pattern tes =
      repeat (canonical_field_counter_view_from_runs schema base_pattern) (length tes).
Proof.
  intros schema base_pattern tes Htes Hactive.
  induction Htes as [|te tes Hte Htes IH]; simpl.
  - reflexivity.
  - rewrite (tx_family_counter_view_law schema base_pattern te Hte Hactive).
    rewrite IH.
    reflexivity.
Qed.

Theorem predicted_tx_family_towers_constant :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_towers base_pattern tes =
      repeat (tx_family_semantic_tower base_pattern) (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  induction Htes as [|te tes Hte Htes IH]; simpl.
  - reflexivity.
  - rewrite (tx_family_semantic_tower_law base_pattern te Hte Hactive).
    rewrite IH.
    reflexivity.
Qed.

Theorem predicted_tx_family_bases_strictly_increasing :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    strictly_increasing tes ->
    runs_positive base_pattern = true ->
    active_run_lengths base_pattern <> [] ->
    strictly_increasing (predicted_tx_family_bases base_pattern tes).
Proof.
  intros base_pattern tes Htes.
  induction tes as [|te1 tes IH]; intros Hinc Hpos Hactive; simpl in *.
  - exact I.
  - destruct tes as [|te2 tes']; simpl in *.
    + exact I.
    + inversion Htes as [|? ? Hte1 Htes']; subst.
      destruct Hinc as [Hlt Hinc'].
      split.
      * destruct
          (tx_family_object_and_base_order_law
             base_pattern te1 te2 Hte1 Hlt Hpos Hactive) as [_ Hbase].
        exact Hbase.
      * apply IH.
        -- exact Htes'.
        -- exact Hinc'.
        -- exact Hpos.
        -- exact Hactive.
Qed.

Theorem tx_family_sweep_prediction_objects_sound :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_objects base_pattern tes =
      repeat
        (sweep_prediction_object (tx_family_sweep_prediction base_pattern tes))
        (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  unfold tx_family_sweep_prediction.
  simpl.
  apply predicted_tx_family_objects_constant.
  - exact Htes.
  - exact Hactive.
Qed.

Theorem tx_family_sweep_prediction_bases_sound :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    strictly_increasing tes ->
    runs_positive base_pattern = true ->
    active_run_lengths base_pattern <> [] ->
    strictly_increasing
      (sweep_prediction_bases (tx_family_sweep_prediction base_pattern tes)).
Proof.
  intros base_pattern tes Htes Hinc Hpos Hactive.
  unfold tx_family_sweep_prediction.
  simpl.
  apply predicted_tx_family_bases_strictly_increasing.
  - exact Htes.
  - exact Hinc.
  - exact Hpos.
  - exact Hactive.
Qed.

Theorem tx_family_semantic_prediction_words_sound :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_frame_words base_pattern tes =
      repeat
        (semantic_prediction_word (tx_family_semantic_prediction base_pattern tes))
        (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  unfold tx_family_semantic_prediction.
  apply predicted_tx_family_frame_words_constant.
  - exact Htes.
  - exact Hactive.
Qed.

Theorem tx_family_semantic_prediction_packets_sound :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_packets base_pattern tes =
      repeat
        (semantic_prediction_packet24 (tx_family_semantic_prediction base_pattern tes))
        (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  unfold tx_family_semantic_prediction.
  apply predicted_tx_family_packets_constant.
  - exact Htes.
  - exact Hactive.
Qed.

Theorem tx_family_semantic_prediction_fields_sound :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_field_views base_pattern tes =
      repeat
        (semantic_prediction_fields (tx_family_semantic_prediction base_pattern tes))
        (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  unfold tx_family_semantic_prediction.
  apply predicted_tx_family_field_views_constant.
  - exact Htes.
  - exact Hactive.
Qed.

Theorem tx_family_semantic_prediction_towers_sound :
  forall base_pattern tes,
    Forall (fun te => 0 < te) tes ->
    active_run_lengths base_pattern <> [] ->
    predicted_tx_family_towers base_pattern tes =
      repeat
        (tx_family_semantic_tower base_pattern)
        (length tes).
Proof.
  intros base_pattern tes Htes Hactive.
  apply predicted_tx_family_towers_constant.
  - exact Htes.
  - exact Hactive.
Qed.

Definition refined_detector_trace (factor : nat) (rs : Runs) : Trace :=
  flatten_runs (scale_runs factor rs).

Definition refined_detector_runs (factor : nat) (rs : Runs) : Runs :=
  rle_trace (refined_detector_trace factor rs).

Definition refined_detector_object (factor : nat) (rs : Runs) : CanonicalRFObject :=
  canonical_normalized_pulse_classes (refined_detector_runs factor rs).

Theorem refined_detector_runs_exact :
  forall factor rs,
    0 < factor ->
    runs_positive rs = true ->
    runs_alternating rs = true ->
    refined_detector_runs factor rs = scale_runs factor rs.
Proof.
  intros factor rs Hfactor Hpos Halt.
  unfold refined_detector_runs, refined_detector_trace.
  rewrite rle_trace_flatten_runs_well_formed.
  - reflexivity.
  - apply runs_positive_scale.
    + exact Hfactor.
    + exact Hpos.
  - apply runs_alternating_scale.
    exact Halt.
Qed.

Theorem refined_detector_recovers_canonical_object :
  forall factor rs,
    0 < factor ->
    runs_positive rs = true ->
    runs_alternating rs = true ->
    active_run_lengths rs <> [] ->
    refined_detector_object factor rs = canonical_rf_object_from_runs rs.
Proof.
  intros factor rs Hfactor Hpos Halt Hactive.
  unfold refined_detector_object, canonical_rf_object_from_runs.
  rewrite refined_detector_runs_exact.
  - apply canonical_normalized_pulse_classes_scale_invariant.
    + exact Hfactor.
    + exact Hactive.
  - exact Hfactor.
  - exact Hpos.
  - exact Halt.
Qed.

Corollary refined_detector_pairwise_equal :
  forall factor1 factor2 rs,
    0 < factor1 ->
    0 < factor2 ->
    runs_positive rs = true ->
    runs_alternating rs = true ->
    active_run_lengths rs <> [] ->
    refined_detector_object factor1 rs = refined_detector_object factor2 rs.
Proof.
  intros factor1 factor2 rs Hfactor1 Hfactor2 Hpos Halt Hactive.
  transitivity (canonical_rf_object_from_runs rs).
  - apply refined_detector_recovers_canonical_object.
    + exact Hfactor1.
    + exact Hpos.
    + exact Halt.
    + exact Hactive.
  - symmetry.
    apply refined_detector_recovers_canonical_object.
    + exact Hfactor2.
    + exact Hpos.
    + exact Halt.
    + exact Hactive.
Qed.

Definition EmitterClass := CanonicalRFObject.

Definition emitter_class_from_runs (rs : Runs) : EmitterClass :=
  canonical_rf_object_from_runs rs.

Definition same_emitter_class_runs (rs1 rs2 : Runs) : Prop :=
  emitter_class_from_runs rs1 = emitter_class_from_runs rs2.

Definition emitter_classes_separated_runs (rs1 rs2 : Runs) : Prop :=
  emitter_class_from_runs rs1 <> emitter_class_from_runs rs2.

Definition cross_receiver_invariant_runs (rs1 rs2 : Runs) : Prop :=
  canonical_rf_object_from_runs rs1 = canonical_rf_object_from_runs rs2.

Definition coarse_cross_receiver_invariant_runs (rs1 rs2 : Runs) : Prop :=
  coarse_canonical_rf_object_from_runs rs1 =
    coarse_canonical_rf_object_from_runs rs2.

Theorem same_emitter_class_runs_refl :
  forall rs,
    same_emitter_class_runs rs rs.
Proof.
  intro rs.
  unfold same_emitter_class_runs.
  reflexivity.
Qed.

Theorem same_emitter_class_runs_sym :
  forall rs1 rs2,
    same_emitter_class_runs rs1 rs2 ->
    same_emitter_class_runs rs2 rs1.
Proof.
  intros rs1 rs2 Hsame.
  unfold same_emitter_class_runs in *.
  symmetry.
  exact Hsame.
Qed.

Theorem same_emitter_class_runs_trans :
  forall rs1 rs2 rs3,
    same_emitter_class_runs rs1 rs2 ->
    same_emitter_class_runs rs2 rs3 ->
    same_emitter_class_runs rs1 rs3.
Proof.
  intros rs1 rs2 rs3 H12 H23.
  unfold same_emitter_class_runs in *.
  congruence.
Qed.

Theorem cross_receiver_invariant_runs_refl :
  forall rs,
    cross_receiver_invariant_runs rs rs.
Proof.
  intro rs.
  unfold cross_receiver_invariant_runs.
  reflexivity.
Qed.

Theorem cross_receiver_invariant_runs_sym :
  forall rs1 rs2,
    cross_receiver_invariant_runs rs1 rs2 ->
    cross_receiver_invariant_runs rs2 rs1.
Proof.
  intros rs1 rs2 Hsame.
  unfold cross_receiver_invariant_runs in *.
  symmetry.
  exact Hsame.
Qed.

Theorem cross_receiver_invariant_runs_trans :
  forall rs1 rs2 rs3,
    cross_receiver_invariant_runs rs1 rs2 ->
    cross_receiver_invariant_runs rs2 rs3 ->
    cross_receiver_invariant_runs rs1 rs3.
Proof.
  intros rs1 rs2 rs3 H12 H23.
  unfold cross_receiver_invariant_runs in *.
  congruence.
Qed.

Theorem cross_receiver_invariant_runs_from_same_emitter_class :
  forall rs1 rs2,
    same_emitter_class_runs rs1 rs2 ->
    cross_receiver_invariant_runs rs1 rs2.
Proof.
  intros rs1 rs2 Hsame.
  unfold same_emitter_class_runs, emitter_class_from_runs in Hsame.
  unfold cross_receiver_invariant_runs, canonical_rf_object_from_runs.
  exact Hsame.
Qed.

Theorem cross_receiver_invariant_runs_separated :
  forall rs1 rs2,
    canonical_rf_object_from_runs rs1 <> canonical_rf_object_from_runs rs2 ->
    ~ cross_receiver_invariant_runs rs1 rs2.
Proof.
  intros rs1 rs2 Hneq Hsame.
  unfold cross_receiver_invariant_runs in Hsame.
  apply Hneq.
  exact Hsame.
Qed.

Theorem coarse_cross_receiver_invariant_runs_refl :
  forall rs,
    coarse_cross_receiver_invariant_runs rs rs.
Proof.
  intro rs.
  unfold coarse_cross_receiver_invariant_runs.
  reflexivity.
Qed.

Theorem coarse_cross_receiver_invariant_runs_sym :
  forall rs1 rs2,
    coarse_cross_receiver_invariant_runs rs1 rs2 ->
    coarse_cross_receiver_invariant_runs rs2 rs1.
Proof.
  intros rs1 rs2 Hsame.
  unfold coarse_cross_receiver_invariant_runs in *.
  symmetry.
  exact Hsame.
Qed.

Theorem coarse_cross_receiver_invariant_runs_trans :
  forall rs1 rs2 rs3,
    coarse_cross_receiver_invariant_runs rs1 rs2 ->
    coarse_cross_receiver_invariant_runs rs2 rs3 ->
    coarse_cross_receiver_invariant_runs rs1 rs3.
Proof.
  intros rs1 rs2 rs3 H12 H23.
  unfold coarse_cross_receiver_invariant_runs in *.
  congruence.
Qed.

Theorem cross_receiver_invariant_runs_implies_coarse :
  forall rs1 rs2,
    cross_receiver_invariant_runs rs1 rs2 ->
    coarse_cross_receiver_invariant_runs rs1 rs2.
Proof.
  intros rs1 rs2 Hsame.
  unfold cross_receiver_invariant_runs in Hsame.
  unfold coarse_cross_receiver_invariant_runs, coarse_canonical_rf_object_from_runs.
  rewrite Hsame.
  reflexivity.
Qed.

Corollary tx_family_members_share_emitter_class :
  forall base_pattern te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern <> [] ->
    same_emitter_class_runs
      (tx_family_member base_pattern te1)
      (tx_family_member base_pattern te2).
Proof.
  intros base_pattern te1 te2 Hte1 Hte2 Hactive.
  unfold same_emitter_class_runs, emitter_class_from_runs.
  apply tx_family_members_share_canonical_object.
  - exact Hte1.
  - exact Hte2.
  - exact Hactive.
Qed.

Corollary tx_families_with_distinct_objects_have_separated_classes :
  forall base_pattern1 base_pattern2 te1 te2,
    0 < te1 ->
    0 < te2 ->
    active_run_lengths base_pattern1 <> [] ->
    active_run_lengths base_pattern2 <> [] ->
    tx_family_object base_pattern1 <> tx_family_object base_pattern2 ->
    emitter_classes_separated_runs
      (tx_family_member base_pattern1 te1)
      (tx_family_member base_pattern2 te2).
Proof.
  intros base_pattern1 base_pattern2 te1 te2 Hte1 Hte2 Hactive1 Hactive2 Hneq.
  unfold emitter_classes_separated_runs, emitter_class_from_runs.
  apply tx_families_with_distinct_objects_stay_separated.
  - exact Hte1.
  - exact Hte2.
  - exact Hactive1.
  - exact Hactive2.
  - exact Hneq.
Qed.

Theorem classify_run_with_base_mark_short_sound :
  forall base n,
    classify_run_with_base base (true, n) = MarkShort ->
    n < 2 * base.
Proof.
  intros base n H.
  unfold classify_run_with_base in H.
  destruct (Nat.ltb n (2 * base)) eqn:Hlt.
  - inversion H; subst.
    apply Nat.ltb_lt in Hlt.
    exact Hlt.
  - discriminate.
Qed.

Theorem classify_run_with_base_mark_long_sound :
  forall base n,
    classify_run_with_base base (true, n) = MarkLong ->
    2 * base <= n.
Proof.
  intros base n H.
  unfold classify_run_with_base in H.
  destruct (Nat.ltb n (2 * base)) eqn:Hlt.
  - discriminate.
  - inversion H; subst.
    apply Nat.ltb_ge in Hlt.
    exact Hlt.
Qed.

Theorem classify_run_with_base_gap_short_sound :
  forall base n,
    classify_run_with_base base (false, n) = GapShort ->
    n < 2 * base.
Proof.
  intros base n H.
  unfold classify_run_with_base in H.
  destruct (Nat.ltb n (2 * base)) eqn:Hlt.
  - inversion H; subst.
    apply Nat.ltb_lt in Hlt.
    exact Hlt.
  - destruct (Nat.ltb n (10 * base)); discriminate.
Qed.

Theorem classify_run_with_base_gap_long_sound :
  forall base n,
    classify_run_with_base base (false, n) = GapLong ->
    2 * base <= n /\ n < 10 * base.
Proof.
  intros base n H.
  unfold classify_run_with_base in H.
  destruct (Nat.ltb n (2 * base)) eqn:Hshort.
  - discriminate.
  - destruct (Nat.ltb n (10 * base)) eqn:Hlong.
    + inversion H; subst.
      split.
      * apply Nat.ltb_ge in Hshort.
        exact Hshort.
      * apply Nat.ltb_lt in Hlong.
        exact Hlong.
    + discriminate.
Qed.

Theorem classify_run_with_base_gap_break_sound :
  forall base n,
    classify_run_with_base base (false, n) = GapBreak ->
    10 * base <= n.
Proof.
  intros base n H.
  unfold classify_run_with_base in H.
  destruct (Nat.ltb n (2 * base)) eqn:Hshort.
  - discriminate.
  - destruct (Nat.ltb n (10 * base)) eqn:Hlong.
    + discriminate.
    + inversion H; subst.
      apply Nat.ltb_ge in Hlong.
      exact Hlong.
Qed.


Definition pulse_class_eqb (x y : PulseClass) : bool :=
  match x, y with
  | MarkShort, MarkShort => true
  | MarkLong, MarkLong => true
  | GapShort, GapShort => true
  | GapLong, GapLong => true
  | GapBreak, GapBreak => true
  | _, _ => false
  end.

Fixpoint pulse_class_list_eqb
    (xs ys : list PulseClass)
    : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' =>
      pulse_class_eqb x y && pulse_class_list_eqb xs' ys'
  | _, _ => false
  end.

Lemma pulse_class_list_eqb_refl :
  forall xs,
    pulse_class_list_eqb xs xs = true.
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - destruct x; simpl; rewrite IH; reflexivity.
Qed.

Fixpoint bool_list_eqb (xs ys : list bool) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => Bool.eqb x y && bool_list_eqb xs' ys'
  | _, _ => false
  end.

Lemma bool_list_eqb_refl :
  forall xs,
    bool_list_eqb xs xs = true.
Proof.
  induction xs as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite Bool.eqb_reflx.
    rewrite IH.
    reflexivity.
Qed.

Record ObservedFrame := {
  observed_class : EmitterClass;
  observed_counter : nat
}.

Definition SecurityState := list ObservedFrame.

Record ObservedDecodedFrame := {
  observed_bits : list bool;
  observed_bits_counter : nat
}.

Definition DecodedSecurityState := list ObservedDecodedFrame.

Definition option_max (x y : option nat) : option nat :=
  match x, y with
  | None, z => z
  | z, None => z
  | Some a, Some b => Some (Nat.max a b)
  end.

Definition FieldCounterState := list FieldCounterView.

Fixpoint max_counter_for_key
    (key : nat)
    (state : FieldCounterState)
    : option nat :=
  match state with
  | [] => None
  | view :: state' =>
      let rest := max_counter_for_key key state' in
      if Nat.eqb key (field_counter_key view) then
        option_max (Some (field_counter_value view)) rest
      else
        rest
  end.

Definition field_counter_fresh
    (state : FieldCounterState)
    (view : FieldCounterView)
    : bool :=
  match max_counter_for_key (field_counter_key view) state with
  | None => true
  | Some max_seen => Nat.ltb max_seen (field_counter_value view)
  end.

Definition record_field_counter_view
    (state : FieldCounterState)
    (view : FieldCounterView)
    : FieldCounterState :=
  view :: state.

Definition decoded_field_counter_step
    (schema : CounterSchema)
    (bits1 bits2 : list bool)
    : Prop :=
  field_counter_step
    (field_counter_view_from_bits schema bits1)
    (field_counter_view_from_bits schema bits2).

Definition decoded_field_counter_fresh
    (schema : CounterSchema)
    (state : FieldCounterState)
    (bits : list bool)
    : bool :=
  field_counter_fresh state (field_counter_view_from_bits schema bits).

Definition canonical_field_counter_fresh_from_runs
    (schema : CounterSchema)
    (state : FieldCounterState)
    (rs : Runs)
    : bool :=
  field_counter_fresh state (canonical_field_counter_view_from_runs schema rs).

Definition decoded_hi16_lo8_fresh
    (state : FieldCounterState)
    (bits : list bool)
    : bool :=
  decoded_field_counter_fresh hi16_lo8_counter_schema state bits.

Definition decoded_prefix12_suffix12_fresh
    (state : FieldCounterState)
    (bits : list bool)
    : bool :=
  decoded_field_counter_fresh prefix12_suffix12_counter_schema state bits.

Inductive PacketSchemaKind :=
| PacketSchemaStatic
| PacketSchemaCounter (schema : CounterSchema).

Definition static_packet_fresh
    (state : list (list bool))
    (bits : list bool)
    : bool :=
  negb (existsb (bool_list_eqb bits) state).

Definition record_static_packet
    (state : list (list bool))
    (bits : list bool)
    : list (list bool) :=
  bits :: state.

Record PacketSchemaState := {
  packet_schema_static_state : list (list bool);
  packet_schema_counter_state : FieldCounterState
}.

Definition packet_schema_fresh_from_bits
    (kind : PacketSchemaKind)
    (state : PacketSchemaState)
    (bits : list bool)
    : bool :=
  match kind with
  | PacketSchemaStatic =>
      static_packet_fresh (packet_schema_static_state state) bits
  | PacketSchemaCounter schema =>
      decoded_field_counter_fresh schema
        (packet_schema_counter_state state) bits
  end.

Definition canonical_packet_schema_fresh_from_runs
    (kind : PacketSchemaKind)
    (state : PacketSchemaState)
    (rs : Runs)
    : bool :=
  packet_schema_fresh_from_bits kind state
    (canonical_frame_bits_from_runs rs).

Definition static_packet_schema_kind : PacketSchemaKind :=
  PacketSchemaStatic.

Definition hi16_lo8_packet_schema_kind : PacketSchemaKind :=
  PacketSchemaCounter hi16_lo8_counter_schema.

Definition prefix12_suffix12_packet_schema_kind : PacketSchemaKind :=
  PacketSchemaCounter prefix12_suffix12_counter_schema.

Lemma max_counter_for_key_record_same :
  forall key ctr state,
    max_counter_for_key key
      (record_field_counter_view state
         {| field_counter_key := key; field_counter_value := ctr |}) =
      option_max (Some ctr) (max_counter_for_key key state).
Proof.
  intros key ctr state.
  unfold record_field_counter_view.
  simpl.
  rewrite Nat.eqb_refl.
  reflexivity.
Qed.

Lemma max_counter_for_key_record_different :
  forall key key' ctr state,
    Nat.eqb key key' = false ->
    max_counter_for_key key
      (record_field_counter_view state
         {| field_counter_key := key'; field_counter_value := ctr |}) =
      max_counter_for_key key state.
Proof.
  intros key key' ctr state Hneq.
  unfold record_field_counter_view.
  simpl.
  rewrite Hneq.
  reflexivity.
Qed.

Theorem unseen_field_counter_key_is_fresh :
  forall key ctr state,
    max_counter_for_key key state = None ->
    field_counter_fresh state {| field_counter_key := key; field_counter_value := ctr |} = true.
Proof.
  intros key ctr state Hnone.
  unfold field_counter_fresh.
  simpl.
  rewrite Hnone.
  reflexivity.
Qed.

Theorem greater_field_counter_is_fresh :
  forall key ctr state max_seen,
    max_counter_for_key key state = Some max_seen ->
    max_seen < ctr ->
    field_counter_fresh state {| field_counter_key := key; field_counter_value := ctr |} = true.
Proof.
  intros key ctr state max_seen Hmax Hlt.
  unfold field_counter_fresh.
  simpl.
  rewrite Hmax.
  apply Nat.ltb_lt.
  exact Hlt.
Qed.

Theorem nonincreasing_field_counter_is_rejected :
  forall key ctr state max_seen,
    max_counter_for_key key state = Some max_seen ->
    ctr <= max_seen ->
    field_counter_fresh state {| field_counter_key := key; field_counter_value := ctr |} = false.
Proof.
  intros key ctr state max_seen Hmax Hle.
  unfold field_counter_fresh.
  simpl.
  rewrite Hmax.
  apply Nat.ltb_ge.
  exact Hle.
Qed.

Theorem exact_field_counter_replay_rejected :
  forall key ctr state,
    field_counter_fresh
      (record_field_counter_view state
         {| field_counter_key := key; field_counter_value := ctr |})
      {| field_counter_key := key; field_counter_value := ctr |} = false.
Proof.
  intros key ctr state.
  unfold field_counter_fresh.
  rewrite max_counter_for_key_record_same.
  simpl.
  destruct (max_counter_for_key key state) as [max_seen|] eqn:Hmax; simpl.
  - apply Nat.ltb_ge.
    apply Nat.le_max_l.
  - apply Nat.ltb_ge.
    lia.
Qed.

Theorem unseen_static_packet_is_fresh :
  forall bits state,
    existsb (bool_list_eqb bits) state = false ->
    static_packet_fresh state bits = true.
Proof.
  intros bits state Hseen.
  unfold static_packet_fresh.
  rewrite Hseen.
  reflexivity.
Qed.

Theorem exact_static_packet_replay_rejected :
  forall bits state,
    static_packet_fresh (record_static_packet state bits) bits = false.
Proof.
  intros bits state.
  unfold static_packet_fresh, record_static_packet.
  simpl.
  rewrite bool_list_eqb_refl.
  reflexivity.
Qed.

Theorem recorded_field_counter_rejects_same_or_lower :
  forall key ctr ctr' state,
    ctr' <= ctr ->
    field_counter_fresh
      (record_field_counter_view state
         {| field_counter_key := key; field_counter_value := ctr |})
      {| field_counter_key := key; field_counter_value := ctr' |} = false.
Proof.
  intros key ctr ctr' state Hle.
  unfold field_counter_fresh.
  rewrite max_counter_for_key_record_same.
  simpl.
  destruct (max_counter_for_key key state) as [max_seen|] eqn:Hmax; simpl.
  - apply Nat.ltb_ge.
    eapply Nat.le_trans.
    + exact Hle.
    + apply Nat.le_max_l.
  - apply Nat.ltb_ge.
    exact Hle.
Qed.

Theorem field_counter_step_is_fresh_after_singleton :
  forall older newer,
    field_counter_step older newer ->
    field_counter_fresh (record_field_counter_view [] older) newer = true.
Proof.
  intros older newer [Hkey Hstep].
  unfold field_counter_fresh, record_field_counter_view.
  simpl.
  destruct older as [older_key older_value].
  destruct newer as [newer_key newer_value].
  simpl in *.
  rewrite <- Hkey.
  rewrite Nat.eqb_refl.
  simpl.
  apply Nat.ltb_lt.
  lia.
Qed.

Theorem decoded_field_counter_step_is_fresh_after_singleton :
  forall schema bits1 bits2,
    decoded_field_counter_step schema bits1 bits2 ->
    decoded_field_counter_fresh schema
      (record_field_counter_view []
         (field_counter_view_from_bits schema bits1))
      bits2 = true.
Proof.
  intros schema bits1 bits2 Hstep.
  unfold decoded_field_counter_fresh.
  apply field_counter_step_is_fresh_after_singleton.
  exact Hstep.
Qed.

Theorem packet_schema_static_replay_rejected :
  forall bits static_state counter_state,
    packet_schema_fresh_from_bits PacketSchemaStatic
      {| packet_schema_static_state := record_static_packet static_state bits;
         packet_schema_counter_state := counter_state |}
      bits = false.
Proof.
  intros bits static_state counter_state.
  unfold packet_schema_fresh_from_bits.
  apply exact_static_packet_replay_rejected.
Qed.

Theorem packet_schema_counter_step_is_fresh_after_singleton :
  forall schema bits1 bits2,
    decoded_field_counter_step schema bits1 bits2 ->
    packet_schema_fresh_from_bits (PacketSchemaCounter schema)
      {| packet_schema_static_state := [];
         packet_schema_counter_state :=
           record_field_counter_view []
             (field_counter_view_from_bits schema bits1) |}
      bits2 = true.
Proof.
  intros schema bits1 bits2 Hstep.
  unfold packet_schema_fresh_from_bits.
  apply decoded_field_counter_step_is_fresh_after_singleton.
  exact Hstep.
Qed.

Fixpoint max_counter_for_bits
    (bits : list bool)
    (state : DecodedSecurityState)
    : option nat :=
  match state with
  | [] => None
  | frame :: state' =>
      let rest := max_counter_for_bits bits state' in
      if bool_list_eqb bits (observed_bits frame) then
        option_max (Some (observed_bits_counter frame)) rest
      else
        rest
  end.

Definition decoded_frame_fresh
    (state : DecodedSecurityState)
    (frame : ObservedDecodedFrame)
    : bool :=
  match max_counter_for_bits (observed_bits frame) state with
  | None => true
  | Some max_seen => Nat.ltb max_seen (observed_bits_counter frame)
  end.

Definition record_decoded_frame
    (state : DecodedSecurityState)
    (frame : ObservedDecodedFrame)
    : DecodedSecurityState :=
  frame :: state.

Fixpoint max_counter_for_class
    (cls : EmitterClass)
    (state : SecurityState)
    : option nat :=
  match state with
  | [] => None
  | frame :: state' =>
      let rest := max_counter_for_class cls state' in
      if pulse_class_list_eqb cls (observed_class frame) then
        option_max (Some (observed_counter frame)) rest
      else
        rest
  end.

Definition frame_fresh
    (state : SecurityState)
    (frame : ObservedFrame)
    : bool :=
  match max_counter_for_class (observed_class frame) state with
  | None => true
  | Some max_seen => Nat.ltb max_seen (observed_counter frame)
  end.

Definition record_frame
    (state : SecurityState)
    (frame : ObservedFrame)
    : SecurityState :=
  frame :: state.

Lemma max_counter_for_class_record_same :
  forall cls ctr state,
    max_counter_for_class cls
      (record_frame state {| observed_class := cls; observed_counter := ctr |}) =
      option_max (Some ctr) (max_counter_for_class cls state).
Proof.
  intros cls ctr state.
  unfold record_frame.
  simpl.
  rewrite pulse_class_list_eqb_refl.
  reflexivity.
Qed.

Lemma max_counter_for_bits_record_same :
  forall bits ctr state,
    max_counter_for_bits bits
      (record_decoded_frame state
         {| observed_bits := bits; observed_bits_counter := ctr |}) =
      option_max (Some ctr) (max_counter_for_bits bits state).
Proof.
  intros bits ctr state.
  unfold record_decoded_frame.
  simpl.
  rewrite bool_list_eqb_refl.
  reflexivity.
Qed.

Lemma max_counter_for_class_record_different :
  forall cls cls' ctr state,
    pulse_class_list_eqb cls cls' = false ->
    max_counter_for_class cls
      (record_frame state {| observed_class := cls'; observed_counter := ctr |}) =
      max_counter_for_class cls state.
Proof.
  intros cls cls' ctr state Hneq.
  unfold record_frame.
  simpl.
  rewrite Hneq.
  reflexivity.
Qed.

Lemma max_counter_for_bits_record_different :
  forall bits bits' ctr state,
    bool_list_eqb bits bits' = false ->
    max_counter_for_bits bits
      (record_decoded_frame state
         {| observed_bits := bits'; observed_bits_counter := ctr |}) =
      max_counter_for_bits bits state.
Proof.
  intros bits bits' ctr state Hneq.
  unfold record_decoded_frame.
  simpl.
  rewrite Hneq.
  reflexivity.
Qed.

Theorem unseen_class_is_fresh :
  forall cls ctr state,
    max_counter_for_class cls state = None ->
    frame_fresh state {| observed_class := cls; observed_counter := ctr |} = true.
Proof.
  intros cls ctr state Hnone.
  unfold frame_fresh.
  simpl.
  rewrite Hnone.
  reflexivity.
Qed.

Theorem unseen_bits_are_fresh :
  forall bits ctr state,
    max_counter_for_bits bits state = None ->
    decoded_frame_fresh
      state {| observed_bits := bits; observed_bits_counter := ctr |} = true.
Proof.
  intros bits ctr state Hnone.
  unfold decoded_frame_fresh.
  simpl.
  rewrite Hnone.
  reflexivity.
Qed.

Theorem greater_counter_is_fresh :
  forall cls ctr state max_seen,
    max_counter_for_class cls state = Some max_seen ->
    max_seen < ctr ->
    frame_fresh state {| observed_class := cls; observed_counter := ctr |} = true.
Proof.
  intros cls ctr state max_seen Hmax Hlt.
  unfold frame_fresh.
  simpl.
  rewrite Hmax.
  apply Nat.ltb_lt.
  exact Hlt.
Qed.

Theorem greater_counter_bits_are_fresh :
  forall bits ctr state max_seen,
    max_counter_for_bits bits state = Some max_seen ->
    max_seen < ctr ->
    decoded_frame_fresh
      state {| observed_bits := bits; observed_bits_counter := ctr |} = true.
Proof.
  intros bits ctr state max_seen Hmax Hlt.
  unfold decoded_frame_fresh.
  simpl.
  rewrite Hmax.
  apply Nat.ltb_lt.
  exact Hlt.
Qed.

Theorem nonincreasing_counter_is_rejected :
  forall cls ctr state max_seen,
    max_counter_for_class cls state = Some max_seen ->
    ctr <= max_seen ->
    frame_fresh state {| observed_class := cls; observed_counter := ctr |} = false.
Proof.
  intros cls ctr state max_seen Hmax Hle.
  unfold frame_fresh.
  simpl.
  rewrite Hmax.
  apply Nat.ltb_ge.
  exact Hle.
Qed.

Theorem exact_replay_rejected :
  forall cls ctr state,
    frame_fresh
      (record_frame state {| observed_class := cls; observed_counter := ctr |})
      {| observed_class := cls; observed_counter := ctr |} = false.
Proof.
  intros cls ctr state.
  unfold frame_fresh.
  rewrite max_counter_for_class_record_same.
  simpl.
  destruct (max_counter_for_class cls state) as [max_seen|] eqn:Hmax; simpl.
  - apply Nat.ltb_ge.
    apply Nat.le_max_l.
  - apply Nat.ltb_ge.
    lia.
Qed.

Theorem exact_decoded_replay_rejected :
  forall bits ctr state,
    decoded_frame_fresh
      (record_decoded_frame state
         {| observed_bits := bits; observed_bits_counter := ctr |})
      {| observed_bits := bits; observed_bits_counter := ctr |} = false.
Proof.
  intros bits ctr state.
  unfold decoded_frame_fresh, record_decoded_frame.
  simpl.
  rewrite bool_list_eqb_refl.
  simpl.
  destruct (max_counter_for_bits bits state) as [max_seen|] eqn:Hmax; simpl.
  - apply Nat.ltb_ge.
    apply Nat.le_max_l.
  - apply Nat.ltb_ge.
    lia.
Qed.

Theorem recorded_frame_rejects_same_or_lower_counter :
  forall cls ctr ctr' state,
    ctr' <= ctr ->
    frame_fresh
      (record_frame state {| observed_class := cls; observed_counter := ctr |})
      {| observed_class := cls; observed_counter := ctr' |} = false.
Proof.
  intros cls ctr ctr' state Hle.
  unfold frame_fresh.
  rewrite max_counter_for_class_record_same.
  simpl.
  destruct (max_counter_for_class cls state) as [max_seen|] eqn:Hmax; simpl.
  - apply Nat.ltb_ge.
    eapply Nat.le_trans.
    + exact Hle.
    + apply Nat.le_max_l.
  - apply Nat.ltb_ge.
    exact Hle.
Qed.

Theorem recorded_decoded_frame_rejects_same_or_lower_counter :
  forall bits ctr ctr' state,
    ctr' <= ctr ->
    decoded_frame_fresh
      (record_decoded_frame state
         {| observed_bits := bits; observed_bits_counter := ctr |})
      {| observed_bits := bits; observed_bits_counter := ctr' |} = false.
Proof.
  intros bits ctr ctr' state Hle.
  unfold decoded_frame_fresh, record_decoded_frame.
  simpl.
  rewrite bool_list_eqb_refl.
  simpl.
  destruct (max_counter_for_bits bits state) as [max_seen|] eqn:Hmax; simpl.
  - apply Nat.ltb_ge.
    eapply Nat.le_trans.
    + exact Hle.
    + apply Nat.le_max_l.
  - apply Nat.ltb_ge.
    exact Hle.
Qed.

