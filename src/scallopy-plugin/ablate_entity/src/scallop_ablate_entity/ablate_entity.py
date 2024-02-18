from typing import *
import scallopy
from scallopy import foreign_predicate, Generator

@foreign_predicate
def ablate_entity(id: scallopy.usize, 
                  token: str, 
                  label: str, 
                  start_idx: scallopy.usize, 
                  end_idx: scallopy.usize, 
                  src: str) -> Generator[float, Tuple]:
  
  yield (0.2, ())
