# subghz-verified

Formalizing sub-GHz OOK pulse classification.

This repository is a dual formalization / exploration engine for sub-GHz radio
experiments predicted by Rocq and common sense, then tested on the bench.

The formalization is split into four files:

- `SubGhzCore.v`: symbolic pulse, token, bit, and packet semantics
- `SubGhzFamilies.v`: family laws, sweep predictions, and replay logic
- `SubGhzObservation.v`: power/IQ observation, certificates, and device-facing theorems
- `SubGhzExtract.v`: OCaml extraction only

The tracked data files are the public bench record that the proofs are
compared against.

## Scope

- Raw IQ to canonical thresholded OOK traces
- Burst detection and onset/offset soundness
- Run extraction and normalized pulse classification
- Timing-family invariance and family separation theorems
- Parse certificates
- Decoded frame-bit, frame-word, and packet semantics
- General packet-structure specs and structure views above the 24-bit word
- Counter-schema taxonomy over decoded frame sequences
- Family-specific packet-schema descriptors and structure catalogs
- Schema-aware freshness for static and counter-shaped packet families
- Threshold-drift, noise-margin, and IQ-energy invariance at the observation layer
- Class-preserving run-jitter invariance at the symbolic layer

## Data

`captures/` contains the direct SDR capture families:

- one quiet control
- `A1B2C3` at `te=200`, `400`, `600`, `800`
- `55AA33` at `te=200`, `400`, `600`, `800`
- `C0FFEE` at `te=250`, `500`, `750`, `1250`
- `DEAD12` at `te=250`, `430`, `910`, `1330`
- `FACE01` at `te=280`, `560`, `840`, `1400`
- `B16B00` at `te=310`, `620`, `930`, `1550`
- `CAFE42` at `te=340`, `680`, `1020`, `1360`
- `1CEB00` at `te=275`, `545`, `1090`, `1635`
- `D15EA5` at `te=290`, `580`, `870`, `1450`
- `ABCD10` at `te=240`, `480`, `960`, `1440`
- `7EA5B0` at `te=260`, `520`, `1040`, `1560`
- `BEEF90` at `te=300`, `600`, `900`, `1500`
- `A5C3D0` at `te=320`, `640`, `960`, `1600`
- `D15EA5` refinement edge case at `te=175`
- `C0FFEE` refinement edge case at `te=175`
- `ABCD10` refinement edge case at `te=160`
- `7EA5B0` refinement edge case at `te=180`
- `BEEF90` refinement edge case at `te=170`
- `A5C3D0` refinement edge case at `te=190`
- `000100` repeated at `te=500`
- `000101` at `te=500`
- `000102`, `000103`, `0001FE`, `0001FF`, `000200`, `000201` at `te=500`
- `C0FFEE` repeat-variation captures at `rep=1`, `3`, `20`
- `BEEF90` repeat-variation captures at `rep=1`, `20`
- `A5C3D0` repeat-variation captures at `rep=1`, `20`
- `ABCD10`, `ABCD11`, `ABCD12`, `ABCD13`, `ABCD1E`, `ABCD1F`, `ABCD20`,
  `ABCD21` at `te=500`
- `7EA5B0`, `7EA5B1`, `7EA5B2`, `7EA5B3`, `7EA5BE`, `7EA5BF`, `7EA5C0`,
  `7EA5C1` at `te=500`
- `BEEF90`, `BEEF91`, `BEEF92`, `BEEF93`, `BEEF9E`, `BEEF9F`, `BEEFA0`,
  `BEEFA1` at `te=500`
- `A5C3D0`, `A5C3D1`, `A5C3D2`, `A5C3D3`, `A5C3DE`, `A5C3DF`, `A5C3E0`,
  `A5C3E1` at `te=500`

Each file is a raw RX IQ capture at `433.92 MHz`, `250 kS/s`, `28.0 dB` gain.
`captures/manifest.csv` records hashes, transmitter parameters, and the
canonical full-file analysis regime used for the published family checks.

`families/manifest.csv` is the project-native family catalog. It records the
canonical class digest, decoded first-frame bits, and the current packet
structure / freshness interpretation for each tracked family.

`replay/manifest.csv` records repeated and repeat-varied project-native captures
used to tie schema-aware freshness and first-packet metamer results to real
emissions, including regime metamers where different analysis regimes recover
the same decoded packet under different class digests.

`schemas/manifest.csv` records the project-native packet-schema probes used to
distinguish simple counter interpretations, carry boundaries, and physically
realized first-packet metamer families.

`structures/manifest.csv` is the packet-schema catalog. It records per-family
structure profiles and the sequence-level structure rows that justify counter,
check, flag, payload, boundary, and metamer interpretations.

`robustness/manifest.csv` records representative threshold-drift, IQ-energy,
phase-walk, additive-noise, and class-preserving jitter checks against tracked
captures.

## Current Results

The current canonical full-file SDR regime uses:

- `window_pairs = 20`
- `analysis_threshold = 131072`

Under that regime:

- the `A1B2C3` family shares digest `19f722404f38089b6308894a201adbf2`
- the `55AA33` family shares digest `b23944cd40c832edea40ca156b5455fe`
- the `C0FFEE` family shares digest `f0409e8cb4d2bdaba1fdd093301be576`
- the `DEAD12` family shares digest `a57783a97009fc13b6e255e487f6e7aa`
- the `FACE01` family shares digest `065e905b4444fd83c706b64c68675320`
- the `B16B00` family shares digest `782fbf6929fb12a9430159f2e512ec13`
- the `CAFE42` family shares digest `9892ff8172cf89f3c143fab27cfafd98`
- the `1CEB00` family shares digest `6b8e88830c92d7161379dbab96d29486`
- the `D15EA5` family shares digest `0ce096fea1adcd848b8e0f359833feca`
- the `ABCD10` family shares digest `06017c95923ccb6afe1fa249c8d798b8`
- the `7EA5B0` family shares digest `c7ae6bd72816cb7860be44be68a3e42b`
- the `BEEF90` family shares digest `f85a7588338de63f1506c84cecb0e026`
- the `A5C3D0` family shares digest `9f6094750e509ccb6fd90af68d59b170`
- the `000100` family shares digest `35b0f28740a34e4e374d4e99cc50303a`
- the `000101` family shares digest `60d799f94711ead89855090b0e62ddf8`
- the `000102` family shares digest `86ee94ceaccb8a4ead0cb91b24dcc8f4`
- the `000103` family shares digest `0e842002045e42849270d9d7e8c7c031`
- the `0001FE` family shares digest `353daff80a3a071c49549eefd9917b68`
- the `0001FF` family shares digest `0b2b64cb0f7473db4762b26d419b4839`
- the `000200` family shares digest `159780e7210c770825e66869544ea553`
- the `000201` family shares digest `a01fa7f07eb20ef666ce6384616151f1`
- all tracked families preserve ordered inferred bases across their `te` sweeps
- the frame decoder recovers `a1b2c3`, `55aa33`, `c0ffee`, `dead12`, `face01`, `b16b00`, `cafe42`, `1ceb00`, `d15ea5`, `000100`, `000101`, `000102`, `000103`, `0001fe`, `0001ff`, `000200`, and `000201`
- the frame decoder also recovers `abcd10`, `abcd11`, `abcd12`, `abcd13`,
  `abcd1e`, `abcd1f`, `abcd20`, `abcd21`, `7ea5b0`, `7ea5b1`, `7ea5b2`,
  `7ea5b3`, `7ea5be`, `7ea5bf`, `7ea5c0`, and `7ea5c1`
- the frame decoder also recovers `beef90`, `beef91`, `beef92`, `beef93`,
  `beef9e`, `beef9f`, `beefa0`, `beefa1`, `a5c3d0`, `a5c3d1`, `a5c3d2`,
  `a5c3d3`, `a5c3de`, `a5c3df`, `a5c3e0`, and `a5c3e1`
- repeated `C0FFEE te500` captures recover the same canonical object and frame word
- `C0FFEE` repeat variation at `rep=1`, `3`, `10`, and `20` recovers the same first packet and structure view
- `BEEF90` repeat variation at `rep=1`, `10`, and `20` recovers the same first packet and structure view
- `A5C3D0` repeat variation at `rep=1`, `10`, and `20` recovers the same first packet and structure view
- repeated `000100 te500` captures recover the same canonical object and frame word
- the `000100 -> 000103` sequence fits both simple counter schemas
- the `0001FE -> 000201` sequence rejects `hi16/lo8` and preserves `prefix12/suffix12`
- the `ABCD10 -> ABCD13` sequence reveals a constant check nibble over a
  low-nibble unit-step counter
- the `ABCD1E -> ABCD21` sequence exposes a boundary nibble change and a
  low-nibble wrap
- the `7EA5B0 -> 7EA5B3` sequence reveals a constant flag and payload above a
  low-nibble unit-step counter
- the `7EA5BE -> 7EA5C1` sequence exposes a payload carry boundary
- the `BEEF90 -> BEEF93` sequence reveals a constant check nibble and payload
  above a low-nibble unit-step counter
- the `BEEF9E -> BEEFA1` sequence exposes a payload carry boundary beneath a
  constant check nibble
- the `A5C3D0 -> A5C3D3` sequence reveals a constant flag and payload above a
  low-nibble unit-step counter
- the `A5C3DE -> A5C3E1` sequence exposes a payload carry boundary beneath a
  constant flag nibble
- `structures/manifest.csv` classifies the tracked family sweeps as constant
  packet families and records the sequence rows where counter, check, flag,
  payload, and boundary behavior becomes visible
- the `D15EA5 te175` edge capture recovers the family under the fine `15 / 98304` regime and drifts under coarser regimes
- the `C0FFEE te175` edge capture also requires the fine `15 / 98304` regime; coarser regimes drift
- the `ABCD10 te160` edge capture is a physically realized regime metamer:
  distinct analysis regimes recover the same decoded packet under different
  class digests
- the `7EA5B0 te180` edge capture is also a physically realized regime metamer
- the `BEEF90 te170` edge capture is also a physically realized regime metamer
- the `A5C3D0 te190` edge capture recovers the family only in finer regimes;
  the canonical regime truncates to the prefix
- deliberate gain, offset, and bounded perturbation checks preserve the canonical object and frame word for `CAFE42` and `1CEB00`
- deliberate gain, offset, and bounded perturbation checks preserve the canonical object and frame word for `D15EA5`
- deliberate gain, offset, and bounded perturbation checks preserve the canonical object and frame word for `BEEF90` and `A5C3D0`
- quarter-turn phase-walk and additive-noise checks preserve the canonical
  object and decoded packet on representative `C0FFEE`, `D15EA5`, `000200`,
  `ABCD10`, `7EA5B0`, `BEEF90`, and `A5C3D0` captures
- the stronger additive-noise sweep remains stable up to amplitude `32` on the
  representative `BEEF90` and `A5C3D0` captures
- upward and downward threshold drift within the proved stability margins preserves decoded packet structure on representative captures
- a synthetic 90 degree IQ rotation preserves window energies, canonical objects, and decoded packets on representative captures
- class-preserving run jitter preserves the decoded packet on representative captures
- the tracked families remain distinct
- generic packet-structure views now lift through the same family and IQ invariance laws as the fixed packet views
- `prefix12/suffix12` is the stronger live counter schema on the tested numeric carry boundaries
