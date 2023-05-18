package tip.analysis

import tip.ast._
import tip.cfg.CfgOps._
import tip.lattices._
import tip.ast.AstNodeData.DeclarationData

import tip.solvers._
import tip.cfg._

/**
 * Base class for the reaching definitions analysis
 */
abstract class ReachingDefinitionsAnalysis(cfg: IntraproceduralProgramCfg)(implicit declData: DeclarationData) extends FlowSensitiveAnalysis[CfgNode](cfg) {

  import AstNodeData._

  val definitions: Set[AstNode] =
    cfg.nodes.flatMap(_.appearingAssignments) union cfg.nodes.flatMap(_.declaredVars)

  val lattice = new MapLattice(cfg.nodes, new PowersetLattice(definitions))

  def transfer(n: CfgNode, s: lattice.sublattice.Element): lattice.sublattice.Element = {
    n match {
      case _: CfgFunEntryNode => lattice.sublattice.bottom
      case r: CfgStmtNode =>
        r.data match {
          case ass: AAssignStmt =>
            ass.left match {
              case id: AIdentifier => removeDefs(s, id) + ass
              case _ => s
            }
          case varr: AVarStmt => s union varr
          case _ => s
        }
      case _ => s
    }
  }

  def removeDefs(s: lattice.sublattice.Element, id: AIdentifier): lattice.sublattice.Element = {
    s.filterNot(node => getVariableId(node).contains(id.value))
  }

  def getVariableId(definition: AstNode): Option[String] = {
    definition match {
      case id: AIdentifierDeclaration =>
        Some(id.value)
      case stmt: AAssignStmt =>
        stmt.left match {
          case id: AIdentifier => Some(id.value)
          case _: AUnaryOp[_] => None
        }
      case _ => None
    }
  }
}

/**
 * Reaching definitions analysis that uses the simple fixpoint solver.
 */
class ReachingDefinitionsAnalysisSimpleSolver(cfg: IntraproceduralProgramCfg)(implicit declarationData: DeclarationData)
  extends ReachingDefinitionsAnalysis(cfg)
    with SimpleMapLatticeFixpointSolver[CfgNode]
    with ForwardDependencies

/**
 * Reaching definitions analysis that uses the worklist solver.
 */
class ReachingDefinitionsAnalysisWorklistSolver(cfg: IntraproceduralProgramCfg)(implicit declarationData: DeclarationData)
  extends ReachingDefinitionsAnalysis(cfg)
    with SimpleWorklistFixpointSolver[CfgNode]
    with ForwardDependencies
