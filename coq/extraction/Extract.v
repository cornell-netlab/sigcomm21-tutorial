Require Coq.extraction.Extraction.
Require Coq.extraction.ExtrOcamlBasic.
Require Coq.extraction.ExtrOcamlNatInt.
Require Coq.extraction.ExtrOcamlNativeString.

Require MiniP4.Syntax.
Require MiniP4.Interp.

Cd "extraction".
Separate Extraction MiniP4.Syntax.
Separate Extraction MiniP4.Interp.
Cd "..".
