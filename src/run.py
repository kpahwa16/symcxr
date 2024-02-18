import os
import glob
import json 
import re
import argparse
import sys
from typing import List, Iterator, Optional
# from allennlp.predictors import Predictor
from allennlp.models.archival import load_archive
from allennlp.common.util import lazy_groups_of
from allennlp.common.checks import ConfigurationError
# from allennlp.data.dataset_readers import MultiTaskDatasetReader
# from allennlp.data.dataset_readers.multitask import MultiTaskDatasetReader
from allennlp.predictors.predictor import Predictor, JsonDict
from allennlp.data import Instance
from allennlp.common.file_utils import cached_path, open_compressed
import dygie.models.dygie as dygie

from utils import construct_graph_prob, det_prob_report
from parse_scl import compare_graphs_prob

"""
The `predict` subcommand allows you to make bulk JSON-to-JSON
or dataset to JSON predictions using a trained model and its
[`Predictor`](../predictors/predictor.md#predictor) wrapper.
"""

from typing import List, Iterator, Optional
import argparse
import sys
import json

from overrides import overrides

from allennlp.commands.subcommand import Subcommand
from allennlp.common import logging as common_logging
from allennlp.common.checks import check_for_gpu, ConfigurationError
from allennlp.common.file_utils import cached_path
from allennlp.common.util import lazy_groups_of
from allennlp.models.archival import load_archive
from allennlp.predictors.predictor import Predictor, JsonDict
from allennlp.data import Instance


def _get_predictor(args: argparse.Namespace) -> Predictor:
    check_for_gpu(args.cuda_device)
    archive = load_archive(
        args.archive_file,
        weights_file=args.weights_file,
        cuda_device=args.cuda_device,
        overrides=args.overrides,
    )

    return Predictor.from_archive(
        archive, args.predictor, dataset_reader_to_load=args.dataset_reader_choice
    )


class _PredictManager:
    def __init__(
        self,
        predictor: Predictor,
        input_file: str,
        output_file: Optional[str],
        batch_size: int,
        print_to_console: bool,
        has_dataset_reader: bool,
    ) -> None:

        self._predictor = predictor
        self._input_file = input_file
        if output_file is not None:
            self._output_file = open(output_file, "w")
        else:
            self._output_file = None
        self._batch_size = batch_size
        self._print_to_console = print_to_console
        if has_dataset_reader:
            self._dataset_reader = predictor._dataset_reader
        else:
            self._dataset_reader = None

    def _predict_json(self, batch_data: List[JsonDict]) -> Iterator[str]:
        if len(batch_data) == 1:
            results = [self._predictor.predict_json(batch_data[0])]
        else:
            results = self._predictor.predict_batch_json(batch_data)
        for output in results:
            yield self._predictor.dump_line(output)

    def _predict_instances(self, batch_data: List[Instance]) -> Iterator[str]:
        if len(batch_data) == 1:
            results = [self._predictor.predict_instance(batch_data[0])]
        else:
            results = self._predictor.predict_batch_instance(batch_data)
        for output in results:
            yield self._predictor.dump_line(output)

    def _maybe_print_to_console_and_file(
        self, index: int, prediction: str, model_input: str = None
    ) -> None:
        if self._print_to_console:
            if model_input is not None:
                print(f"input {index}: ", model_input)
            print("prediction: ", prediction)
        if self._output_file is not None:
            self._output_file.write(prediction)

    def _get_json_data(self) -> Iterator[JsonDict]:
        if self._input_file == "-":
            for line in sys.stdin:
                if not line.isspace():
                    yield self._predictor.load_line(line)
        else:
            input_file = cached_path(self._input_file)
            with open(input_file, "r") as file_input:
                for line in file_input:
                    if not line.isspace():
                        yield self._predictor.load_line(line)

    def _get_instance_data(self) -> Iterator[Instance]:
        if self._input_file == "-":
            raise ConfigurationError("stdin is not an option when using a DatasetReader.")
        elif self._dataset_reader is None:
            raise ConfigurationError("To generate instances directly, pass a DatasetReader.")
        else:
            yield from self._dataset_reader.read(self._input_file)

    def run(self) -> None:
        has_reader = self._dataset_reader is not None
    
        index = 0
        if has_reader:
            for batch in lazy_groups_of(self._get_instance_data(), self._batch_size):
                for model_input_instance, result in zip(batch, self._predict_instances(batch)):
                    self._maybe_print_to_console_and_file(index, result, str(model_input_instance))
                    index = index + 1
        else:
            for batch_json in lazy_groups_of(self._get_json_data(), self._batch_size):
                for model_input_json, result in zip(batch_json, self._predict_json(batch_json)):
                    self._maybe_print_to_console_and_file(
                        index, result, json.dumps(model_input_json)
                    )
                    index = index + 1

        if self._output_file is not None:
            self._output_file.close()


def _predict(args: argparse.Namespace) -> None:
    common_logging.FILE_FRIENDLY_LOGGING = args.file_friendly_logging

    predictor = _get_predictor(args)

    if args.silent and not args.output_file:
        print("--silent specified without --output-file.")
        print("Exiting early because no output will be created.")
        sys.exit(0)

    manager = _PredictManager(
        predictor,
        args.input_file,
        args.output_file,
        args.batch_size,
        not args.silent,
        args.use_dataset_reader,
    )
    manager.run()

    # has_reader = _dataset_reader is not None
    # index = 0
    # if has_reader:
    #     for batch in lazy_groups_of(self._get_instance_data(), self._batch_size):
    #         for model_input_instance, result in zip(batch, self._predict_instances(batch)):
    #             self._maybe_print_to_console_and_file(index, result, str(model_input_instance))
    #             index = index + 1
    # else:
    #     for batch_json in lazy_groups_of(self._get_json_data(), self._batch_size):
    #         for model_input_json, result in zip(batch_json, self._predict_json(batch_json)):
    #             self._maybe_print_to_console_and_file(
    #                 index, result, json.dumps(model_input_json)
    #             )
    #             index = index + 1

def get_file_list(path):
    
    """Gets path to all the reports (.txt format files) in the specified folder, and
    saves it in a temporary json file
    
        Args:
            path: Path to the folder containing the reports
    """
    
    file_list = [item for item in glob.glob(f"{path}/*.txt")]
    
    # Number of files for inference at once depends on the memory available.
    ## Recemmended to use no more than batches of 25,000 files
    
    with open('./temp_file_list.json', 'w') as f:
        json.dump(file_list, f)


def preprocess_report(file_name, text):
    
    """ Load up the files mentioned in the temporary json file, and
    processes them in format that the dygie model can take as input.
    Also save the processed file in a temporary file.
    """

    sen = re.sub('(?<! )(?=[/,-,:,.,!?()])|(?<=[/,-,:,.,!?()])(?! )', r' ',text).split()
    temp_dict = {}

    temp_dict["doc_key"] = file_name
    
    ## Current way of inference takes in the whole report as 1 sentence
    temp_dict["sentences"] = [sen]

    return temp_dict
    

def preprocess_reports():
    
    """ Load up the files mentioned in the temporary json file, and
    processes them in format that the dygie model can take as input.
    Also save the processed file in a temporary file.
    """
    
    file_list = json.load(open("./temp_file_list.json"))
    final_list = []
    for idx, file in enumerate(file_list):

        temp_file = open(file).read()
        sen = re.sub('(?<! )(?=[/,-,:,.,!?()])|(?<=[/,-,:,.,!?()])(?! )', r' ',temp_file).split()
        temp_dict = {}

        temp_dict["doc_key"] = file
        
        ## Current way of inference takes in the whole report as 1 sentence
        temp_dict["sentences"] = [sen]

        final_list.append(temp_dict)

        if(idx % 1000 == 0):
            print(f"{idx+1} reports done")
    
    print(f"{idx+1} reports done")
    
    with open("./temp_dygie_input.json",'w') as outfile:
        for item in final_list:
            json.dump(item, outfile)
            outfile.write("\n")

def construct_pred_graph(rep_dict, result):

    node_rel = []
    edge_rel = []
    children = {}
    children_rel = []
    nodes = []
    report = {}

    entities = get_entity(result['ner']['predictions'][0], result['relation']['predictions'][0], rep_dict['sentences'][0])
    report['entities'] = entities
    graph = construct_graph_prob(report)

    return graph

    # for node in G.nodes():
    #     node_rel.append((1.0, (node, G.nodes[node]['tokens'], G.nodes[node]['label'], phase)))

    # for from_nid, to_nid in G.edges():
    #     rel_name = G[from_nid][to_nid]['relation']
    #     edge_rel.append((1.0, (to_nid, rel_name, from_nid, phase)))
    #     if not from_nid in children:
    #         children[from_nid] = []
    #     children[from_nid].append(to_nid)
    
    # for from_nid, to_nid_ls in children.items():
    #     child_des = "Nil()"
    #     for to_nid in to_nid_ls:
    #         child_des = f"Cons({to_nid}, {child_des})" 
    #     children_rel.append((1.0, (from_nid, child_des, phase)))

    
def run_inference(model_path, data_path, scl_file_path, cuda):
    
    """ Runs the inference on the processed input files. Saves the result in a
    temporary output file
    
    Args:
        model_path: Path to the model checkpoint
        cuda: GPU id
    
    """

    archive = load_archive(
        model_path,
        weights_file="",
        cuda_device=cuda,
        overrides="",
    )

    predictor = Predictor.from_archive(
        archive,
        "dygie.predictors.dygie.DyGIEPredictor",
    )

    predictor._dataset_reader.setup(data_path)

    dataset_reader = predictor._dataset_reader
    
    # TODO: Add shuffling here
    for file_name, datapoint in dataset_reader.dataset.items():
        rep_dict = preprocess_report(file_name, datapoint['text'])
        instance = dataset_reader.text_to_instance(rep_dict)
        result = predictor.predict_instance(
                instance
                )
        
        pred_graph = construct_pred_graph(rep_dict, result)
        gt_report = det_prob_report(datapoint)
        gt_graph = construct_graph_prob(gt_report)
        match_score = compare_graphs_prob(gt_graph, pred_graph, scl_file_path)
        
        # TODO: Just compare the match score against 1.0 will give you the loss
        
        break

    print('here')
    # output = manager.run()
    # os.system(f"allennlp predict {model_path} {data_path} \
    #         --predictor dygie --include-package dygie \
    #         --use-dataset-reader \
    #         --output-file {out_path} \
    #         --cuda-device {cuda} \
    #         --silent")

def postprocess_reports():
    
    """Post processes all the reports and saves the result in train.json format
    """
    final_dict = {}

    file_name = f"./temp_dygie_output.json"
    data = []

    with open(file_name,'r') as f:
        for line in f:
            data.append(json.loads(line))

    for file in data:
        postprocess_individual_report(file, final_dict)
    
    return final_dict

def postprocess_individual_report(file, final_dict, data_source=None):
    
    """Postprocesses individual report
    
    Args:
        file: output dict for individual reports
        final_dict: Dict for storing all the reports
    """
    
    try:
        temp_dict = {}

        temp_dict['text'] = " ".join(file['sentences'][0])
        n = file['predicted_ner'][0]
        r = file['predicted_relations'][0]
        s = file['sentences'][0]
        temp_dict["entities"] = get_entity(n,r,s)
        temp_dict["data_source"] = data_source
        temp_dict["data_split"] = "inference"

        final_dict[file['doc_key']] = temp_dict
    
    except:
        print(f"Error in doc key: {file['doc_key']}. Skipping inference on this file")

# TODO: modify this function so that it takes in LLM-CXR's input probability    
def get_entity(n,r,s):
    
    """Gets the entities for individual reports
    
    Args:
        n: list of entities in the report
        r: list of relations in the report
        s: list containing tokens of the sentence
        
    Returns:
        dict_entity: Dictionary containing the entites in the format similar to train.json 
    
    """

    dict_entity = {}
    rel_list = [item['span1'] for item in r]
    ner_list = [(item['span_start'], item['span_end']) for item in n]
    for idx, item in enumerate(n):
        temp_dict = {}
        start_idx, end_idx, label = item['span_start'], item['span_end'], item['predicted_label']
        temp_dict['tokens'] = " ".join(s[start_idx:end_idx+1])
        temp_dict['label'] = label
        temp_dict['start_ix'] = start_idx
        temp_dict['end_ix'] = end_idx
        temp_dict['prob'] = item['predicted_label_probability']
        rel = []
        relation_idx = [i for i,val in enumerate(rel_list) if val==(start_idx, end_idx)]
        for i,val in enumerate(relation_idx):
            obj = r[i]['span2']
            lab = r[i]['label']
            prob = r[i]['probability']
            try:
                object_idx = ner_list.index(obj) + 1
            except:
                continue
            rel.append([prob, (lab,str(object_idx))])
        temp_dict['relations'] = rel
        dict_entity[str(idx+1)] = temp_dict
    
    return dict_entity

def cleanup():
    """Removes all the temporary files created during the inference process
    
    """
    os.system("rm temp_file_list.json")
    os.system("rm temp_dygie_input.json")
    os.system("rm temp_dygie_output.json")

def run(model_path, data_path, scl_file_path, cuda):
    
    # print("Getting paths to all the reports...")
    # get_file_list(data_path)
    # print(f"Got all the paths.")
    
    # print("Preprocessing all the reports...")
    # preprocess_reports()
    # print("Done with preprocessing.")
    
    print("Running the inference now... This can take a bit of time")
    run_inference(model_path, data_path, scl_file_path, cuda)
    print("Inference completed.")
    
    # print("Postprocessing output file...")
    # final_dict = postprocess_reports()
    # print("Done postprocessing.")
    
    # print("Saving results and performing final cleanup...")
    # cleanup()
    
    # with open(out_path,'w') as outfile:
    #     json.dump(final_dict, outfile)

if __name__ == '__main__':
    model_dir = os.path.abspath(os.path.join(os.path.abspath(__file__), '../../models'))
    checkpoint_path = os.path.join(model_dir, 'model.tar.gz')

    data_dir = os.path.abspath(os.path.join(os.path.abspath(__file__), '../../data'))
    med_data_dir = os.path.join(data_dir, 'medical_imaging')
    data_path = os.path.join(med_data_dir, 'dev.json')

    scl_dir = os.path.abspath(os.path.join(os.path.abspath(__file__), '../scl'))
    scl_file_path = os.path.join(scl_dir, 'medical_match_v2.scl')

    cuda_device = -1
    
    run(checkpoint_path, data_path, scl_file_path, cuda_device)
