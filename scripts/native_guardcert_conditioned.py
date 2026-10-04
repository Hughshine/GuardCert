"""Run the complete scalar/rectangular/deep regression with the search compiler."""
import native_guardcert as combined
import native_guardcert_paths as paths
import native_affine_nest_condition_search as conditioned


def main():
    combined.COMPILER=conditioned.COMPILER
    combined.WORK=combined.ROOT/'build/native-guardcert-conditioned'
    combined.check_build=conditioned.check_build
    compile_run=combined.compile_run
    def without_search(name,mode,syntax,extra,expected):
        return compile_run(name,mode,syntax,
            extra|{'GUARDCERT_AFFINE_CONDITION_SEARCH':'disabled'},expected)
    combined.compile_run=without_search
    combined.main()
    paths.main()

if __name__=='__main__':main()
