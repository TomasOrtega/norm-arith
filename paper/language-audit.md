# ASD-STE100 review of the manuscript

This is a complete editorial pass over the stated prose scope against Issue 9
(15 January 2025), not an ASD certification. The result is STE-based explanatory
prose with the explicit mathematical and research-format exceptions below.
**Unqualified conformance to all of ASD-STE100 is not established.** In
particular, the standard's technical-noun permission does not by itself permit
mathematical adjectives in predicates, mathematical quantifiers, or proof
imperatives in descriptive text.

The official reference is the [Issue 9 rules and dictionary](https://www.asd-ste100.org/assets/files/ASD-STE100_ISSUE9.pdf).
The complete standard was consulted outside this repository. This package does
not redistribute its rules, examples, dictionary, or an extracted word database.
The matrix below paraphrases the review criteria and records project evidence.

## Scope and evidence

The pass covers the abstract, main text, appendix prose, captions, headings,
generated implementation/evaluation statuses, and explanatory example text.
Bibliographic titles, official names, mathematical notation, literal source
blocks, and Lean identifiers retain their source spelling. They are identified
as names, technical terms, or formal material, not counted as ordinary English.

Every prose paragraph was reviewed for its argument, articles, references,
voice, tense, vocabulary, and word roles. The vocabulary ledger is
[vocabulary-review.tsv](vocabulary-review.tsv): it lists every distinct prose
surface word, its intended part of speech and sense, and the dictionary,
technical-category, or exception basis. The occurrence contexts and counts are
in [output/language-candidates.json](output/language-candidates.json). A word's
presence in this ledger does not approve all its possible meanings or roles.

The general-vocabulary review used dictionary headwords, approved verb forms,
adjective forms, meanings, and parts of speech. It also inspected words that
have both approved and unapproved entries. For example:

- *fast/faster* and *slow/slower* are adjective comparisons of compilation
  rates, not the unapproved adverb uses.
- *linear*, *linearly*, *sound*, *right*, *warm*, *patch*, and *layer* do not get
  permission from unrelated physical dictionary senses. Mathematical and
  software meanings have their own ledger classifications. The final caption
  avoids *warm* altogether.
- The reason conjunction is *because*, not the time conjunction *since*.
- Mathematical *solve*, *satisfy*, *realize*, *imply*, and *normalize* are
  declared technical verbs. *Validate* names the computer proof-validation
  operation. Their nominal forms are separately identified technical nouns.
- General uses of *therefore*, *genuine*, *retain*, *require*, *obtain*, *provide*,
  and *choose* were rewritten. A general unapproved word was not made a
  technical term merely to avoid an edit.

The build produces a current-corpus hash and compares it with
[language-review.json](language-review.json). A changed sentence can change a
word's meaning even if it adds no new words. Thus both a vocabulary gap and a
changed corpus invalidate the recorded pass. New census or timing prose needs
another complete pass before the record is renewed.

## Controlled terminology and exceptions

These are permissions for specific concepts, not a free extension of the
ordinary vocabulary. The ledger gives the complete surface-word inventory.

| Class | Concepts and intended use | Basis |
| --- | --- | --- |
| Mathematical nouns | Vector atom, coefficient, affine scalar term, norm, seminorm, span, basis, quotient, complement, support, polyhedron, vertex, feasibility, counterexample, norm-value realization | Rule 1.5 category 7; rule 1.6 for noun components |
| Mathematical verbs | Assign a formal vector, solve a rational system, enumerate supports, normalize a vector term, satisfy a constraint, realize norm values, prove or imply a proposition, maximize a scalar objective, group timing observations, calibrate block length, omit a jackknife block | Rule 1.12 category 3(a); the same tense and voice review as other verbs |
| Computing nouns | Tactic, certificate, kernel, elaboration, frontend, backend, source span, source patch, import, dependency artifact, compiler output, serialization, search budget, enumeration status | Rule 1.5 category 19 |
| Computing verbs | Compile a module, extract an observation, encode an equality, validate a proof, render a PDF, return a status, sort paths | Rule 1.12 category 2 |
| Scientific-method nouns | Pilot, census, paired pass, confidence interval, source universe, line accounting, baseline, protocol, sampling unit, ratio of means, confirmatory experiment, timing block, bootstrap, BCa transformation, jackknife acceleration, empirical quantile, bias-correction tie | Rule 1.5 category 7, restricted to the specified experiment |
| Names, labels, numbers | Lean, mathlib, NeurIPS, ASD-STE100, people, JSON, C, TeX, fixed status labels, numerals, seconds | Rule 1.5 categories 9, 10, 11, 19 |

E1 — **Mathematical property and relational syntax.** Formal statements retain
precise mathematical adjectives, their predicative uses, quantifier phrases,
comparison syntax, and connective uses such as *exactly when* and *equivalently*.
Examples are “the cost is nonnegative,” “the columns are independent,” “$b$ is
rational,” “strictly positive,” and quantification *over* a class. The physical
approved senses of *linear*, *weak*, or *sound* do not license these meanings.
Inside a defined mathematical noun, the noun-category permission applies.
Outside that noun, these are explicit mathematical-genre exceptions.
The same boundary covers stochastic independence in the timing model.
The numerical adjective *even* means divisible by two, not physically smooth.

E2 — **Proof language.** Mathematical derivations use “Let,” “Suppose,”
“Select,” “Define,” and similar proof instructions. These are conventional
mathematical constructions. They are not maintenance procedures for the reader.
They are an exception to the exclusion of imperatives from descriptive prose.
Their sentence lengths and condition order were still reviewed. The evaluation
protocol's actual instructions are procedural text and use the section 5 rules.

E3 — **Specified artifact and research properties.** The paper retains exact
properties and labels such as *complete*, *partial*, *original*, *pinned*,
*semantic*, *source-backed*, *incomplete*, and *resource-exhausted* for the
specified theorem, baseline, source snapshot, or program status. Most occur as
components of defined technical nouns. The ledger flags the predicative and
other uses that need a research-genre exception. This also covers formal
location metaphors for source containment. It does not license decorative
synonyms in general prose. The timing model's *representative* blocks
are a specified statistical assumption, not an approved general adjective.
*Empirical quantile*, *block length*, and *logical processor* are context-bound
technical nouns. *Bias-corrected and accelerated* is the full established name
introduced with its short form *BCa*.

E4 — **Formal and preserved material.** Equations, quantified formal syntax,
Lean code, identifiers, literal archived source, bibliographic titles, and
unchanged official labels retain their content. This prose review does not
rewrite them to force dictionary coverage. Imported Lean snippets pass a fresh
Lean compilation; that is mathematical/software validation, not language
validation.

The formal *abstraction* gives independent interpretations to scalar and vector
atoms. *Norm-free expression*, *opaque subterm*, *reified syntax*, and *internal
semantics* name that specific frontend/model boundary. Mathematical completeness
does not restore the hidden operations of those expressions. These new uses
received the same contextual dictionary/POS review as the existing prose.

The longer technical name *seminormed additive commutative group* appears in
full before the paper defines the shorter form *additive group*. The shorter
form has only that local meaning. Other compound terms use at most three
words, or hyphens for a defined unit. *Lean kernel* and *seminorm kernel* refer
to different concepts; context and the glossary distinguish them.

## Rule-by-rule applicability and result

“Reviewed” means that the stated scope was inspected and avoidable violations
were edited. “Exception” identifies retained material rather than a claim that
the rule is satisfied without qualification. Rule numbers refer to Issue 9.

| Rule | Project criterion | Result and concrete evidence |
| --- | --- | --- |
| 1.1 | Limit lexical choices to the dictionary and declared terminology | Reviewed with the complete surface-word/context ledger; E1–E4 are explicit boundaries. |
| 1.2 | Match each general word's approved grammatical role | Reviewed; adjective *faster/slower*, verb *validate*, noun *check*. Technical and exceptional roles are distinct ledger columns. |
| 1.3 | Match the intended general meaning | Reviewed; physical *warm*, *layer*, *patch*, *linear*, and *right* were not silently accepted for software or mathematical meanings. E1/E3 apply. |
| 1.4 | Limit inflection and comparison forms | Reviewed; *faster/slower/longer* checked against their headwords. Mathematical predicates and adverbs have E1 treatment. |
| 1.5 | Identify a subject-field noun category | Reviewed; the table above assigns mathematical, computing, experimental, numerical, and name categories. |
| 1.6 | Restrict unapproved components to their technical concepts | Reviewed; *normal form*, *affine term*, *source patch*, *original variant* have context-bound meanings. E1/E3 flag uses beyond noun components. |
| 1.7 | Do not convert a technical noun into an undeclared verb | Reviewed; *has support* replaces *is supported*. Mathematical and computing verbs have separate category assignments. |
| 1.8 | Use established subject terminology | Reviewed against Lean/mathlib, the cited norm-arithmetic work, and the exact mathematical definitions in the paper. |
| 1.9 | Prefer concise, intelligible names | Reviewed; *atom*, *certificate*, *pilot*, and *census* have explicit meanings. No decorative technical aliases. |
| 1.10 | Exclude regional or slang terminology | Reviewed; no slang or regional technical nouns. Named systems retain official spelling. |
| 1.11 | Keep technical names stable | Reviewed; *norm certificate* shortens to *certificate*. The two kernel meanings are distinguished. The additive-group alias is explicit. |
| 1.12 | Declare subject-specific actions | Reviewed; mathematical and computing verb classes above. Their permission does not approve unrelated ordinary uses. |
| 1.13 | Keep technical verb and noun roles distinct | Reviewed; *compile/compilation*, *normalize/normalization*, *validate/validation*; nominal terms have separate noun classifications. |
| 1.14 | Use US spelling | Reviewed; *normalization*, *program*, *artifact*, *cataloged* checked. Fixed titles and imported code retain original spelling. |
| 2.1 | Keep noun groups short | Reviewed throughout prose and captions; long groups were split, for example “mean total times for the affected files.” |
| 2.2 | Introduce a long necessary name and give a clear short form | Reviewed; the four-word additive-group name appears before its explicit two-word alias. Hyphenated defined units keep relationships clear. |
| 3.1 | Use allowed forms for general verbs | Reviewed against the dictionary; the ledger names inflected forms such as *decreases*, *occurs*, and *tries*. Technical verbs follow the same form review. |
| 3.2 | Avoid prohibited tense constructions | Reviewed; present description, simple past build record, proof infinitives, and E2 imperatives. No perfect or progressive prose construction remains. |
| 3.3 | Use participles as modifiers with a clear noun | Reviewed; *validated certificate*, *archived pilot*, *selected patch*, *observed vector*. Mathematical property predicates have E1 treatment. |
| 3.4 | Avoid complex auxiliary chains | Reviewed all finite verb groups. Modals express protocol requirements; no perfect/passive/progressive chains. |
| 3.5 | Restrict ambiguous verbal -ing clauses | Reviewed; replaced “Finding,” “Combining and scaling,” and “before extracting” clauses. *Timing*, *sampling*, and *encoding* name declared processes. E1 covers necessary mathematical forms. |
| 3.6 | Prefer an explicit active agent | Reviewed; “the build imports/extracts/renders,” “Lean validates,” “the report counts.” Mathematical predicates are not treated as hidden-agent passives. |
| 3.7 | State actions with verbs | Reviewed; *compile*, *validate*, *record*, *select*, *count* express operations directly. Defined mathematical nouns remain nouns. |
| 4.1 | Keep syntax short and relations explicit | Reviewed every paragraph; the length aid has no open candidates. Longer explanations were divided without changing quantifiers. |
| 4.2 | Keep necessary words and avoid contractions | Reviewed; no contractions or telegram-like prose. Formula notation has E4 treatment. |
| 4.3 | Use a list where it improves a complex presentation | Reviewed; finite constraints use aligned mathematical display rather than a long sentence. Preserved code is not prose. |
| 4.4 | Make logical connections visible | Reviewed; *because*, *thus*, explicit conditions, and repeated technical subjects connect proof steps. E1 covers mathematical connectives. |
| 4.5 | Supply articles or clear demonstratives | Reviewed noun phrases and pronoun references; “the minimum,” “the independent columns,” “a feasible point.” Formal variables have E4 treatment. |
| 5.1 | Keep procedural instructions within 20 words | Reviewed protocol imperatives and proof steps. Formula-containing proof text has E2/E4 treatment; ordinary procedural instructions fit the limit. |
| 5.2 | Avoid multiple independent instructions in one step | Reviewed line accounting, census, and timing instructions. A selected list of protocol fields is one selection action. |
| 5.3 | Use commands for actual instructions | Reviewed; *Count*, *Keep*, *Select*, *Do not discard*. E2 distinguishes mathematical proof instructions. |
| 5.4 | Give a necessary condition before its command | Reviewed conditional proof and protocol instructions; *For equality conclusions*, *If...*, *Before the run*. |
| 5.5 | Keep notes informative | Not separately applicable: no procedural note boxes. Status paragraphs state information and do not hide instructions. |
| 6.1 | Introduce information in stages | Reviewed: problem, grammar, finite theorem, proof idea, implementation, census, compilation, limits; full derivation follows in appendices. |
| 6.2 | Use stable organizing terms | Reviewed section references and repeated subjects: *constraints*, *certificate*, *pilot*, *census*, *confirmatory timing*. |
| 6.3 | Keep descriptive sentences within 25 prose words | Reviewed with section 8 counting principles. Automated formula placeholders are only a length aid; E1/E4 preserve formal expressions. No open prose-length candidates. |
| 6.4 | Group related statements into paragraphs | Reviewed; proof construction, scalar decision, pilot accounting, and timing have separate paragraphs. |
| 6.5 | Keep one subject per paragraph | Reviewed all paragraphs, including generated statuses and captions. Splits separate certificate construction from scalar handling and pilot text from checked generalizations. |
| 6.6 | Keep each paragraph within six sentences | Reviewed; paragraph splits resolve every reported candidate. Generated status prose is included. Proof displays do not conceal extra sentences. |
| 7.1 | Label actual safety hazards | Not applicable: no safety instructions or hazardous activity. Software failure states are not physical safety warnings. |
| 7.2 | State a safety command or condition clearly | Not applicable for the same reason. |
| 7.3 | Explain an identified safety risk | Not applicable for the same reason. |
| 8.1 | Use permitted prose punctuation | Reviewed; removed every prose semicolon. Mathematical delimiters and literal Lean source have E4 treatment. |
| 8.2 | Connect a defined compound unit clearly | Reviewed *real-space*, *zero-norm*, *source-backed*, *resource-exhausted*, *nonoverlapping*. Hyphens do not replace definitions. |
| 8.3 | Restrict parenthetical material to useful identification or explanation | Reviewed; mathematical variable groups, aliases, and units explain or identify. No nested prose digressions. |
| 8.4 | Treat a list-introducing colon as a sentence boundary for counts | Reviewed displayed-constraint introductions and protocol lists. No hidden long prose list. |
| 8.5 | Apply the standard's parenthesis convention in prose counts | Reviewed; the automated tokenizer is conservative and not the conformance authority. Formal parentheses fall under E4. |
| 8.6 | Count numbers, identifiers, names, and preserved labels consistently | Reviewed; numbers/macros and names are single reference units. Equations are E4 formal spans, not purported ordinary STE words. |
| 8.7 | Count a hyphenated unit consistently | Reviewed; the aid counts each such unit once. Rule 2 review also checks that the compound has a clear meaning. |
| 9.1 | Recast a sentence if a synonym changes its meaning | Reviewed; changed sentence structures for *require*, *preserve*, *obtain*, *provide*, and *therefore*. No blind global synonym substitution. |
| 9.2 | Check ordinary grammar and intended meaning | Reviewed the full prose and each vocabulary context; no word-list membership claim replaces this contextual pass. |
| 9.3 | Avoid newly coined phrasal verbs | Reviewed; the mathematical *pull back* sentence now uses the separately declared verb *induce*. No casual phrasal-verb substitutes. |
| 9.4 | Keep terminology, counting units, and reporting style consistent | Reviewed source/variant labels, compilation stages, pilot versus census status, timing statistic, and proof-code accounting. |

The eight general recommendations were also reviewed: dependent clauses use
*that* when helpful; *with* has a clear relationship; pronouns have nearby
antecedents; *this* refers to a stated object or observation; no false-friend
substitution; no unnecessary Latin abbreviation; no gender assumptions; and
possessives identify the actual owner. These recommendations are not additional
numbered rules.

## Reproducible review boundary

`python3 paper/audit.py` writes length candidates, the complete occurrence
ledger, vocabulary gaps, and corpus/ledger hashes. It does not perform an
ASD-certified grammar or semantic analysis. After a complete contextual pass,
`python3 paper/audit.py --record-review` records the reviewed snapshot. This
operation is an editorial assertion, not an automatic proof of language
conformance. The build checks that the record still matches.

A fresh final build must also check the six examples, regenerate all data,
check references and glyphs, and render every page for visual review. A passing
Lean build or a four-page layout cannot establish STE compliance. A new census
summary, timing result, or changed claim invalidates the language snapshot and
must receive the same full prose review.

The final scope pass clarifies independent scalar atoms and unsupported vector
subterms without extending the mathematical theorem to hidden operation
semantics. It also reviews the native-library attribution paragraph: changed
imports can change observed compilation time, so an algorithm comparison needs
matched runtime/import conditions. Both paragraphs are included in the current
corpus-bound review.


## Timing-methods and hardware renewal

The 20 October 2026 renewal reviews the complete current prose corpus, with
special attention to the changed confirmatory-methods and hardware paragraphs.
It keeps all 53 applicability results above. The mathematical proof, checked
source excerpts, generated pending statuses, and archived negative pilot remain
unchanged. No new census or confirmatory result is asserted.

The dictionary/POS pass replaces general *both* with *the two*, *whole* with
*full*, and *orders* with *sequences*. It avoids general *assume*, *concern*,
*justify*, and software *filtered* rather than assigning them unrelated
approved meanings. The verb *group* and the set relation *overlap* have
explicit statistical/mathematical roles. *Removes* has a declared technical-verb
sense for deleting source lines or omitting a jackknife block. The mathematical
*weight* of a tie does not use the dictionary's gravitational meaning.

The argument/POS pass distinguishes a timing block from a source proof block,
stochastic independence from linear independence, and a statistical model from
the theorem's realization model. The ledger records each context. The resampling
and jackknife units are the same full blocks. The probability transformation's
citation does not attribute half-ties or linear empirical quantiles to the
original BCa paper. The paragraph states model assumptions and the limit of
pilot diagnostics without asserting a coverage theorem. The primary-source
method record is [benchmark-statistics.md](../docs/research/benchmark-statistics.md).

The syntax pass checks active subjects, present-tense descriptions, procedure
imperatives, articles, nearby references, and one topic per paragraph. All new
descriptive sentences fit 25 words. The grouping and pre-run selection
instructions fit 20 words. Each paragraph has at most six sentences. Formal
$K=N/b$ notation retains E4 treatment. The count $K$ is the number of
resampling units, not the number of individual files or paired passes.

The hardware names and GB unit retain official spelling. The prose uses the
recorded Apple M4 Max, MacBook Pro, 36 GB, and 14-logical-processor observations;
[metadata/machine-profile-20261020.json](metadata/machine-profile-20261020.json)
and [metadata/logical-processors.json](metadata/logical-processors.json) preserve
their sources. The author line is now *Anonymous Authors*. This renewal covers
source prose only: no new PDF layout or build validation is asserted.


## Corrected census-patch renewal

The current pass includes the finished full-source protocol, retained extraction
gaps, source-verified corrected patch, literal Uniform source example, and the
separate superseded experiment. It does not assert a new timing result.
All 53 criteria above were reapplied to the current main text, appendix,
generated statuses, captions, and every new occurrence context.

The denominator is the full tracked file inventory. Incomplete files remain
visible. The 99 known eligible observations without terminal outcomes are not
an exhaustive count of unseen goals. Unlocated and unresolved node counters
are also coverage limits, not counts of distinct unsupported goals. The pass
checks these quantifiers together with the table captions and the source
eligibility definition. No discarded observation becomes a tactic success.

The norm example is the actual selected Uniform entry. Its literal source
spans and combined verification are bound in the generated provenance.
The generalized archived FDeriv example and slower prototype pilot remain
separate in the appendix. The source-style correction has its own transparent
record and does not transfer the superseded patch's timing estimate.

The dictionary/POS pass replaces *charge* with *count* or *include* in general
line-accounting prose, avoiding the approved electrical meaning of *charge*.
It replaces general *reasons* with *causes*, *earlier* with the exact
*superseded* artifact status, and avoids *needs*, *remain*, *describe*, and
*save* as unapproved general verbs. The approved *try*, *measure*, *change*,
*do*, and *have* forms retain their stated senses. Mathematical *fewer* is an
E1 numerical comparison. Technical terms such as *source-style*, *single-line*,
*node*, *fragment*, *format correction*, and *net line saving* have specific
ledger meanings. Possessives identify the actual source file or mathlib project.

The syntax pass checks active subjects, procedure and description boundaries,
articles, temporal references, and one topic per paragraph. It checks source
counts rather than display-line wrapping. Atom assignments no longer suggest
linear independence. The discussion of separate opaque interpretations keeps
its formal abstraction meaning. No new long-sentence or long-paragraph
exception is introduced. This is the same qualified STE review, not external
ASD certification. Final timing prose will need a new corpus-bound renewal.


## Final confirmatory-result renewal

The final pass supersedes the earlier pending-timing snapshots. It covers the
completed corrected study, abstract result, source-case explanation, all new
result captions, calibration diagnostics, per-file timing table, build-cost
limits, and portable-example status. All 53 rules and the eight general
recommendations above were reapplied to the complete current prose corpus.

The pass checks the numerical claim's subject and denominator: compilation
across the affected files with built dependencies, rather than all individual
files or a full dependency/native build. The Uniform slowdown stays explicit.
The interval uses full timing blocks and the conditional independent-block
model. The actual calibration review excludes average speed levels and uses
serial, drift, and sequence diagnostics. Six pilot blocks do not prove
independence. The new figures come from validated final inputs; no estimate
from the superseded patch or prototype pilot supplies the final result.

The past-tense/POS pass distinguishes ordinary approved forms such as *was*,
*were*, *included*, and *kept* from declared computing operations such as
*loaded*, *emitted*, *froze*, and *passed*. Statistical *grouped* and arithmetic
*divided* have category 3(a) treatment. *Met* is the explicit numerical
satisfaction predicate for the frozen speed rule, not a general dictionary
permission. *Native-library*, *full-pass*, and *block-length* are defined
technical components. *Serial*, *drift*, *significance*, *interval*, and
*independence* keep their statistical meanings. Physical *warm* and *cold* do
not license computing-cache meanings: the prose instead says built
dependencies and an unmeasured build without dependency/native artifacts.

The final pass checks active subjects, simple past or present descriptions,
articles, comparison scope, nearby references, and paragraph topics. Literal
source and mathematical notation keep E4 treatment. The record is still a
qualified project editorial review, not unqualified ASD conformance or external
certification. The final PDF needs its separate reference, font, layout, and
all-page visual checks.

## Expanded-manuscript final renewal

The 21 October revision explains bounded quantified specialization and generic
pseudometric constraints. The real-space finite-characterization theorem and
its mathematical scope are unchanged. The review separates the earlier full
census from the targeted subset and the composed source patch. Preparation is
visible in the Strong Law example. Historical timings give no estimate for the
expanded tactic.

The current contextual pass reviewed new mathematical and computing terms,
explicit fact control, rollback, alias filtering, fixed resource limits, and
native-import attribution. The vocabulary ledger records their precise senses.
General uses of *retain*, *require*, and *provide* were replaced by simpler
wording. The new terms do not approve unrelated senses or give dictionary
permission to mathematical predicates.

The final pass reviews the actual 310-line, 87-replacement, 46-file patch and its
new timing evidence. It checks every current main/appendix paragraph, heading,
generated status, and table caption against the 53-rule matrix and the vocabulary
contexts. Source quotations, equations, names and identifiers keep their declared
formal treatment. The language aid has no open length candidates or vocabulary
gaps. The record binds the complete current prose and ledger hashes.

The scope review distinguishes census-generated replacements from replacements
composed outside the census. Some of the latter only supply explicit facts.
Preparation is counted when present. The assistance disclosure explicitly names
artificial-intelligence coding agents; *assisted* has a declared research-genre
exception, without a general technical-verb permission.

The numerical review distinguishes a 1.0724 time ratio from a percentage decrease
in elapsed time. It keeps all 40 pairs and seven slower files. Prominent interval
statements say *conditional*. The observed +4.26%/+5.14% half-run duration changes,
the independent representative-block model, and the noisy pilot diagnostics
remain visible. The power snapshots do not establish continuous conditions.

The mathematical/POS review keeps *conditional*, *relative*, and the finite-file
quantifier *every* within their stated statistical meanings. The sentence that
the interval *remains conditional* has an explicit mathematical-grammar exception.
It is not a general dictionary approval for *remain*. Physical terms identify
recorded power/thermal quantities and system labels. The native-import paragraph
does not attribute all observed savings to the tactic algorithm.

The initial prototype pilot, calibration pilot, and confirmatory experiment have
separate roles. The final corpus-bound pass is STE-based explanatory writing,
with the declared mathematical and research-format exceptions. It is not
unqualified ASD-STE100 conformance or external certification.
