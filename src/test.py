import scallopy
import os 

def main(provenance, scl_file_path):
    ctx = scallopy.ScallopContext(
        provenance=provenance,
    )

    ctx.import_file(scl_file_path)
    ctx.run()
    output = list(ctx.relation('same_entity'))
    print('here')

if __name__ == "__main__":
    provenance = "unit"
    scl_file_path = os.path.abspath(os.path.join(os.path.abspath(__file__), "../../src/scl/medical_match.scl"))
    main(provenance, scl_file_path)