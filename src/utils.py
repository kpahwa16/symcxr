import json
import os
import networkx as nx
import copy
import random
import torch

# Convert a deterministic report into a probabilistic one
def rand_prob_report(report):
    for entity, entity_info in report['entities'].items():
        entity_prob = torch.rand(1)
        entity_info['prob'] = entity_prob
        new_rela_ls = []
        for rela in entity_info['relations']:
            rela_prob = torch.rand(1)
            new_rela_ls.append((rela_prob, rela))
        entity_info['relations'] = new_rela_ls
    return report

# Convert a deterministic report into a probabilistic one
def det_prob_report(report):
    for entity, entity_info in report['entities'].items():
        entity_prob = torch.tensor(1.0)
        entity_info['prob'] = entity_prob
        new_rela_ls = []
        for rela in entity_info['relations']:
            rela_prob = torch.tensor(1.0)
            new_rela_ls.append((rela_prob, rela))
        entity_info['relations'] = new_rela_ls
    return report

# Construct a graph 
def construct_graph(report):
    G = nx.DiGraph()

    for entity_name, entity_info in report['entities'].items():

        new_node_info = copy.deepcopy(entity_info)
        new_node_info['relations'] = []

        for ori_rela, ori_node in  entity_info['relations']:
            new_node_info['relations'].append([ori_rela, int(ori_node)])
        
        G.add_node(int(entity_name), **new_node_info)
        
        for relation in entity_info['relations']:
            # assert relation[0] == 'located_at'
            G.add_edge(int(entity_name), int(relation[1]), relation=relation[0])
    
    return G

def construct_graph_prob(report):
    G = nx.DiGraph()

    for entity_name, entity_info in report['entities'].items():

        new_relas = []

        for prob, (ori_rela, ori_node) in entity_info['relations']:
            new_relas.append((prob, [ori_rela, int(ori_node)]))
        entity_info['relations'] = new_relas

        G.add_node(int(entity_name), **entity_info)
        
        for prob, relation in entity_info['relations']:
            G.add_edge(int(entity_name), int(relation[1]), relation=relation[0], prob=prob)
    
    return G


def construct_relations_prob(G, phase):
    node_rel = []
    edge_rel = []
    children = {}
    children_rel = []

    for node in G.nodes():
        node_rel.append((1.0, (node, G.nodes[node]['tokens'], G.nodes[node]['label'], phase)))

    for from_nid, to_nid in G.edges():
        rel_name = G[from_nid][to_nid]['relation']
        edge_rel.append((1.0, (to_nid, rel_name, from_nid, phase)))
        if not from_nid in children:
            children[from_nid] = []
        children[from_nid].append(to_nid)
    
    for from_nid, to_nid_ls in children.items():
        child_des = "Nil()"
        for to_nid in to_nid_ls:
            child_des = f"Cons({to_nid}, {child_des})" 
        children_rel.append((1.0, (from_nid, child_des, phase)))

    return node_rel, edge_rel, children_rel

def construct_relations(G, phase):
    node_rel = []
    edge_rel = []
    children = {}
    children_rel = []

    for node in G.nodes():
        node_rel.append((node, G.nodes[node]['tokens'], G.nodes[node]['label'], phase))

    for from_nid, to_nid in G.edges():
        rel_name = G[from_nid][to_nid]['relation']
        edge_rel.append((to_nid, rel_name, from_nid, phase))
        if not from_nid in children:
            children[from_nid] = []
        children[from_nid].append(to_nid)
    
    for from_nid, to_nid_ls in children.items():
        child_des = "Nil()"
        for to_nid in to_nid_ls:
            child_des = f"Cons({to_nid}, {child_des})" 
        children_rel.append((from_nid, child_des, phase))

    return node_rel, edge_rel, children_rel
    

def gen_isomorphic_graph(graph):
    new_graph = nx.DiGraph()

    ori_nodes = list(graph.nodes())
    shuffled_nodes = copy.deepcopy(ori_nodes)
    random.shuffle(shuffled_nodes)

    node_lookup = {ori: new for ori, new in zip(ori_nodes, shuffled_nodes)}
    
    for node in graph.nodes():
        new_node_info = copy.deepcopy(graph.nodes[node])
        new_node_info['relations'] = []

        for ori_rela, ori_node in graph.nodes[node]['relations']:
            new_node_info['relations'].append([ori_rela, node_lookup[ori_node]])
        
        new_graph.add_node(node_lookup[node], **new_node_info)
    
    for edge in graph.edges():
        edge_info = graph[edge[0]][edge[1]]
        new_graph.add_edge(node_lookup[edge[0]], node_lookup[edge[1]], **edge_info)

    return new_graph, node_lookup

