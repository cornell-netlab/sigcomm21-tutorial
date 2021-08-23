Require Coq.extraction.Extraction.
Require Coq.extraction.ExtrOcamlBasic.
Require Coq.extraction.ExtrOcamlNatInt.
Require Coq.extraction.ExtrOcamlNativeString.

Require MiniP4.Syntax.

Cd "extraction".
Separate Extraction MiniP4.Syntax.
Cd "..".
