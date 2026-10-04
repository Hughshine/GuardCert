"""Check variable scalar rewrites through the multiversion compiler entry."""
import native_variable_cancel as scalar
import native_variable_cancel_paths as paths
import native_affine_nest_runtime_versions as versions

def main():
    scalar.WORK=scalar.ROOT/'build/native-variable-cancel-versions'
    scalar.main([('versions',versions)])
    paths.main({'versions':versions})

if __name__=='__main__':main()
