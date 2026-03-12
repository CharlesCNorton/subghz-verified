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
- `D15EA5` refinement edge case at `te=175`
- `000100` repeated at `te=500`
- `000101` at `te=500`

Each file is a raw RX IQ capture at `433.92 MHz`, `250 kS/s`, `28.0 dB` gain.
`captures/manifest.csv` records hashes, transmitter parameters, and the
canonical full-file analysis regime used for the published family checks.

`families/manifest.csv` is the project-native family catalog. It records the
canonical class digest and the decoded first-frame bits for each tracked family.

`replay/manifest.csv` records repeated project-native captures used to tie the
decoded replay layer to real repeated emissions.

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
- the `000100` family shares digest `35b0f28740a34e4e374d4e99cc50303a`
- the `000101` family shares digest `60d799f94711ead89855090b0e62ddf8`
- all tracked families preserve ordered inferred bases across their `te` sweeps
- the frame decoder recovers `a1b2c3`, `55aa33`, `c0ffee`, `dead12`, `face01`, `b16b00`, `cafe42`, `1ceb00`, `d15ea5`, `000100`, and `000101`
- repeated `C0FFEE te500` captures recover the same canonical object and frame word
- repeated `000100 te500` captures recover the same canonical object and frame word
- the `D15EA5 te175` edge capture recovers the family under the fine `15 / 98304` regime and drifts under coarser regimes
- deliberate gain, offset, and bounded perturbation checks preserve the canonical object and frame word for `CAFE42` and `1CEB00`
- deliberate gain, offset, and bounded perturbation checks preserve the canonical object and frame word for `D15EA5`
- the tracked families remain distinct
