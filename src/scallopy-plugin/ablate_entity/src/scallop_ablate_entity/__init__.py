import scallopy

from .config import setup_arg_parser, configure
from .ablate_entity import ablate_entity

def load_into_context(ctx: scallopy.Context):
  ctx.register_foreign_predicate(ablate_entity)
