# Authorship and source attribution

Hailey Collet (HaileyCollet@gmail.com) is the sole human author of this submission. The contribution is offered under Apache-2.0, with upstream licenses and attribution retained.

I started and directed the project, chose the targets and sources, and organized the research and critical comparisons across models. I initially wanted a compact, self-contained proof with a stronger constant. I later gave the stronger bound more priority. I selected the separate `4/33` branch and challenged its dependence on earlier zero-free arguments, which helped clarify what self-containment required. I decided what to retain, check and combine.

The detailed analytic derivations and much of the drafting were developed with AI assistance, mainly GPT6-Pro and non-Pro Astra, with contributions from GPT 6.1 Sol, Grok 4.7 and Gemini 3.1 Pro. AI assistance was also used for Lean formalization. Some research prompts were AI-written and selected or adapted by me.

The formalization builds on [OpenAI/math](https://github.com/openai/math), specifically its `family003` QRH development, including the Hecke family over `ℚ(ζ₃)`, analytic interfaces and coarse `7/8` initialization. It also adapts Akash Levy's [weighted-numerator proof](https://github.com/akashlevy/QuasiRiemannTracker), pinned to revision `2fd60c0926b66ea18d7436f5ed55250fd006ab5d`. Source notices identify these adaptations. Akash Levy's contribution and the original OpenAI mathematics retain their own authorship.

The variable-κ moment uses the completed zero-slot moment from this project's earlier `4/33` branch. That branch supplied a compact self-contained manuscript; its compactness is a manuscript contribution, not a description of the size of this Lean development. The present submission contains the quartic endpoint and the auxiliary common-profile moment interface described in the README.

