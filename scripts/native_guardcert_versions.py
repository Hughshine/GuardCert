"""Run existing deep, rectangular and scalar services with the version entry."""
import native_guardcert as combined
import native_guardcert_paths as paths
import native_affine_nest_runtime_versions as versions

def main():
    combined.COMPILER=versions.COMPILER
    combined.WORK=combined.ROOT/'build/native-guardcert-versions'
    combined.check_build=versions.check_build
    compile_run=combined.compile_run
    def single_profile(name,mode,syntax,extra,expected):
        return compile_run(name,mode,syntax,extra|{'GUARDCERT_AFFINE_CONDITION_SEARCH':'disabled'},expected)
    combined.compile_run=single_profile
    combined.main()
    paths.main()

if __name__=='__main__':main()
