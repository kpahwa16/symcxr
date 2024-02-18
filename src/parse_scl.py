import json
import os
import networkx as nx
import random
import copy
import itertools
import errno
import functools
import signal
import scallopy
import torch

from utils import construct_graph, construct_graph_prob, construct_relations, construct_relations_prob, rand_prob_report
class TimeoutError(Exception):
    pass

def timeout(seconds=10, error_message=os.strerror(errno.ETIME)):
    def decorator(func):
        def _handle_timeout(signum, frame):
            raise TimeoutError(error_message)

        @functools.wraps(func)
        def wrapper(*args, **kwargs):
            signal.signal(signal.SIGALRM, _handle_timeout)
            signal.alarm(seconds)
            try:
                result = func(*args, **kwargs)
            finally:
                signal.alarm(0)
            return result

        return wrapper

    return decorator

def save_rels(rels, file_name):
    auxilary = ["import \"medical_match_v2.scl\""]
    content = []

    for rel_name, rel_values in rels.items():
        rel_ls = []

        for ct, rel in enumerate(rel_values):
            if rel_name != 'children':
                rel_ls.append(str(rel).replace("'", '"'))
            else: 
                child_def = f"const c_{rel[2]}_{ct} = {rel[1]}"
                rel_ls.append(f"({rel[0]}, c_{rel[2]}_{ct}, " + "\"" + rel[2] + "\")")
                auxilary.append(child_def)

        content.append(
            f"rel {rel_name}=" + '{' +  ', \n'.join(rel_ls) + '}'
        )

    content = ['\n'.join(auxilary)] + content
    with open(file_name, 'w') as f:
        f.write('\n\n'.join(content))

def add_root(G, root_id = 0):
    assert not root_id in G.nodes()

    forest_roots = [n for n,d in G.in_degree() if d==0] 
    root_info = {'start_ix': -1, 'end_ix': -1, 'label': 'root', 'tokens': 'root'}
    G.add_node(root_id, **root_info)

    for n in forest_roots:
        G.add_edge(root_id, n, relation="root")

    return G

def compare_graphs(G_gt, G_pred, scl_file_path, save_rel_path=None):

    # Construct root nodes for both graphs 
    G_gt = add_root(G_gt)
    G_pred = add_root(G_pred)

    ctx = scallopy.Context()
    ctx.import_file(scl_file_path)

    node_gt_rel, edge_gt_rel, children_gt_rel = construct_relations(G_gt, 'GT')
    node_pred_rel, edge_pred_rel, children_pred_rel = construct_relations(G_pred, 'PRED')

    rels = {'entity': node_gt_rel + node_pred_rel,
            'rela': edge_gt_rel + edge_pred_rel,
            'children': children_gt_rel + children_pred_rel}

    if not save_rel_path is None:
        save_rels(rels, save_rel_path)
        exit()

    for rel_name in rels:
        ctx.add_facts(rel_name, rels[rel_name])

    ctx.run()
    result = list(ctx.relation('same_tree'))
    if (0, 0) in result:
        return True
    else:
        return False


def compare_graphs_prob(G_gt, G_pred, scl_file_path, save_rel_path=None, prov='difftopkproofs'):

    # Construct root nodes for both graphs 
    G_gt = add_root(G_gt)
    G_pred = add_root(G_pred)

    ctx = scallopy.Context(provenance=prov) 
    ctx.import_file(scl_file_path)

    node_gt_rel, edge_gt_rel, children_gt_rel = construct_relations_prob(G_gt, 'GT')
    node_pred_rel, edge_pred_rel, children_pred_rel = construct_relations_prob(G_pred, 'PRED')

    rels = {'entity': node_gt_rel + node_pred_rel,
            'rela': edge_gt_rel + edge_pred_rel,
            'children': children_gt_rel + children_pred_rel}

    if not save_rel_path is None:
        save_rels(rels, save_rel_path)
        exit()

    for rel_name in rels:
        ctx.add_facts(rel_name, rels[rel_name])

    ctx.run()
    result = list(ctx.relation('same_tree'))
    for res_prob, res in result:
        if res == (0, 0):
            return res_prob
    
    return torch.tensor(0.0)
    


if __name__ == "__main__":
    data_dir = os.path.abspath(os.path.join(os.path.abspath(__file__), '../../data'))
    scl_dir = os.path.abspath(os.path.join(os.path.abspath(__file__), '../scl'))

    pred_dir = os.path.join(data_dir, 'Radgraph')
    gt_dir = os.path.join(data_dir, 'medical_imaging')
    check_split = 'test'

    if check_split == 'train':  
        gt_data_path = os.path.join(gt_dir, 'train.json')
        pred_data_path = os.path.join(pred_dir, 'train-pred.json')
    else:
        gt_data_path = os.path.join(gt_dir, 'test.json')
        pred_data_path = os.path.join(pred_dir, 'test-pred.json')

    scl_file_path = os.path.join(scl_dir, 'medical_match_v2.scl')
    # save_rel_path = os.path.join(scl_dir, 'example_1.scl')
    save_rel_path = None

    gt_data_points = json.load(open(gt_data_path))
    pred_data_points = json.load(open(pred_data_path))

    gt_graph_reports = {}
    all_outcomes = []
    timeout_ct = 0

    for file_name, label_info in gt_data_points.items():
        gt_graph_reports[file_name] = []
        for tag, report in label_info.items():
            
            # For each manual labeler, create a parse version of the report
            if 'labeler' in tag:
                report = rand_prob_report(report)
                G = construct_graph_prob(report)
                gt_graph_reports[file_name].append(G)
            
            elif 'entities' in tag:
                report = rand_prob_report(label_info)
                G = construct_graph_prob(report)
                gt_graph_reports[file_name].append(G)

    pred_graph_reports = {}
    for file_name, label_info in pred_data_points.items():
        pred_graph_reports[file_name] = []
        for tag, report in label_info.items():
            
            # For each manual labeler, create a parse version of the report
            if 'labeler' in tag:
                report = rand_prob_report(report)
                G = construct_graph_prob(report)
                pred_graph_reports[file_name].append(G)

            elif 'entities' in tag:
                report = rand_prob_report(label_info)
                G = construct_graph_prob(report)
                pred_graph_reports[file_name].append(G)

    
    for file_name, pred_graphs in pred_graph_reports.items():

        # if not file_name == "p15/p15024484/s55357745.txt":
        #     continue

        print(file_name)
        gt_graph = gt_graph_reports[file_name]

        # for ct1, g1 in enumerate(pred_graphs):
        #     for ct2, g2 in enumerate(gt_graphs):
        #         # iso_g2, node_lookup = gen_isomorphic_graph(g2)
        #         # iso_g1, node_lookup = gen_isomorphic_graph(g1)
        #         outcome = compare_graphs(g1, g2)
        #         print(outcome)
        # g1, node_lookup_1 = gen_isomorphic_graph(gt_graph[0])
        # g2, node_lookup_2 = gen_isomorphic_graph(gt_graph[0])
        

        outcome = compare_graphs_prob(gt_graph[0], pred_graphs[0], scl_file_path, save_rel_path)
        all_outcomes.append(outcome)
        
        print(outcome)

    same_ct = len([i for i in all_outcomes if i])
    different_ct =  len([i for i in all_outcomes if not i])

    print(same_ct)
    print(different_ct)
    print(timeout_ct)
    print('end')