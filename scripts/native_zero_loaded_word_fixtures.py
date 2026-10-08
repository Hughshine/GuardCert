"""Successor same-C fixtures: zero RMW with separate and aliasing headers."""
import native_loaded_word_fixtures as historical
prior = historical.prior
NAMES, MARKED, COUNTS = historical.NAMES, historical.MARKED, historical.COUNTS
function_body, printer_for_gcc = historical.function_body, historical.printer_for_gcc
closing_brace, dispatch_sites, model = historical.closing_brace, historical.dispatch_sites, historical.model
INPUTS = [*historical.INPUTS, (0,3,31,2,5,0), (0,31,31,31,5,0), (0,2,31,32,5,0)]
CASES = [(kind,*values) for kind in range(len(NAMES)) for values in INPUTS]
# Unsupported alpha+1 would change these headers and grow the source loop.
# The original matrix already checks that unsupported source's refusal.
CASES += [(kind,0,2,3,2,-7,0) for kind in range(5)]
CASES += [(kind,0,2,3,3,-7,0) for kind in range(5)]
HELPERS = ["scripts/native_zero_loaded_word_fixtures.py", *historical.HELPERS]

def source_text(markers=True):
    text = historical.source_text(markers)
    return text[:text.rindex("int main(void)")] + "int main(void){" + "".join(
        "tensor_case("+",".join(map(prior.literal,case))+");" for case in CASES)+"return 0;}\n"

def expected_output(column=False):
    return "".join(model(case,column)for case in CASES)
