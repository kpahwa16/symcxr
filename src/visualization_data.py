import json
import os
import networkx as nx
from parse import construct_graph

def construct_graph_json(G):
    graph = {}
    graph['nodes'] = {}
    graph['edges'] = []

    for node in G.nodes():
        name = G.nodes[node]['tokens']
        info = G.nodes[node]
        info['text'] = name
        graph['nodes'][node] = info
    
    for (n1, n2) in G.edges():
        edge_info = G[n1][n2]['relation']
        graph['edges'].append((n1, n2, edge_info, 0))

    return graph

def construct_datapoint(G_gt, G_pred, file_name):
    graph_gt_json = construct_graph_json(G_gt)
    graph_pred_json = construct_graph_json(G_pred)
    datapoint = {}
    datapoint['graph_gt'] = graph_gt_json
    datapoint['graph_pred'] = graph_pred_json
    datapoint['file_name'] = file_name
    return datapoint

if __name__ == "__main__":
    data_dir = os.path.abspath(os.path.join(os.path.abspath(__file__), '../../data'))
    pred_dir = os.path.join(data_dir, 'Radgraph')
    gt_dir = os.path.join(data_dir, 'medical_imaging')
    check_split = 'test'
    
    vis_data_dir = os.path.abspath(os.path.join(os.path.abspath(__file__), '../../radgraph-viz/data'))
    save_dir = os.path.join(vis_data_dir, f'dp_vis_{check_split}.json')

    if check_split == 'train':  
        gt_data_path = os.path.join(gt_dir, 'train.json')
        pred_data_path = os.path.join(pred_dir, 'train-pred.json')
    else:
        gt_data_path = os.path.join(gt_dir, 'test.json')
        pred_data_path = os.path.join(pred_dir, 'test-pred.json')

    gt_data_points = json.load(open(gt_data_path))
    pred_data_points = json.load(open(pred_data_path))

    gt_graph_reports = {}
    all_outcomes = []
    timeout_ct = 0
    json_dps = []

    for file_name, label_info in gt_data_points.items():
        gt_graph_reports[file_name] = []
        for tag, report in label_info.items():
            # For each manual labeler, create a parse version of the report
            if 'labeler' in tag:
                G = construct_graph(report)
                gt_graph_reports[file_name].append(G)
            
            elif 'entities' in tag:
                G = construct_graph(label_info)
                gt_graph_reports[file_name].append(G)

    pred_graph_reports = {}
    for file_name, label_info in pred_data_points.items():
        pred_graph_reports[file_name] = []
        for tag, report in label_info.items():
            # For each manual labeler, create a parse version of the report
            if 'labeler' in tag:
                G = construct_graph(report)
                pred_graph_reports[file_name].append(G)

            elif 'entities' in tag:
                G = construct_graph(label_info)
                pred_graph_reports[file_name].append(G)

    
    for file_name, pred_graphs in pred_graph_reports.items():

        # if not file_name == "p10/p10002013/s55941092.txt":
        #     continue

        print(file_name)
        gt_graphs = gt_graph_reports[file_name]
        for gt_graph in gt_graphs:
            for pred_graph in pred_graphs:
                json_dps.append(construct_datapoint(gt_graph, pred_graph, file_name))

    json.dump(json_dps, open(save_dir, 'w'))
    print('end')