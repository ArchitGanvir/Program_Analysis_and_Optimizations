#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/IR/LegacyPassManager.h"

#include <map>
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CFG.h"

using namespace llvm;

namespace {
struct cons_eval : public ModulePass {
  static char ID;
  cons_eval() : ModulePass(ID) {}

  const std::pair<int, bool> TOP = std::make_pair(-1, false), BOTTOM = std::make_pair(0, false);

  std::map <Function *, std::map<Value *, std::pair<int, bool>>> arguments;
  std::map <Function *, std::pair<int, bool>> return_values;
  std::map <Function *, std::set<Function *>> callers;
  std::set <Function *> worklist;
  std::map <Function *, std::map<Instruction *, std::map<Value *, std::pair<int, bool>>>> out;

  std::pair<int, bool> meet(std::pair<int, bool> pair1, std::pair<int, bool> pair2)
  {
    if (pair1 == BOTTOM || pair2 == BOTTOM)
    {
      pair1 = BOTTOM;
    }
    else if (pair1 == TOP && pair2 == TOP)
    {
      pair1 = TOP;
    }
    else if (pair1 == TOP)
    {
      pair1 = pair2;
    }
    else if (pair2 != TOP && pair1 != pair2)
    {
      pair1 = BOTTOM;
    }

    return pair1;
  }

  std::map<Value *, std::pair<int, bool>> meet(std::map<Value *, std::pair<int, bool>> map1, std::map<Value *, std::pair<int, bool>> map2)
  {
    for (auto &pair : map1)
    {
      map1[pair.first] = meet(map1[pair.first], map2[pair.first]);
    }

    return map1;
  }

  std::map<Value *, std::pair<int, bool>> calculate_effect(Instruction *I, Instruction *prev_instruction)
  {
    std::map<Value *, std::pair<int, bool>> effect;
    Value *op1, *op2;
    std::pair<int, bool> value1, value2;
    Function *F;
    std::map<Value *, std::pair<int, bool>> actual_arguments, old_arguments;

    if (prev_instruction)
    {
      effect = out[prev_instruction->getFunction()][prev_instruction];
    }
    else
    {
      effect = out[I->getFunction()][I];
    }

    if (I->isBinaryOp())
    {
      op1 = I->getOperand(0);
      if (dyn_cast<Constant>(op1) == NULL)
      {
        value1 = effect[op1];
      }
      else
      {
        value1 = std::make_pair(dyn_cast<Constant>(op1)->getUniqueInteger().getSExtValue(), true);
      }

      op2 = I->getOperand(1);
      if (dyn_cast<Constant>(op2) == NULL)
      {
        value2 = effect[op2];
      }
      else
      {
        value2 = std::make_pair(dyn_cast<Constant>(op2)->getUniqueInteger().getSExtValue(), true);
      }

      if (value1 == BOTTOM || value2 == BOTTOM)
      {
        effect[I] = BOTTOM;
      }
      else if (value1 == TOP || value2 == TOP)
      {
        effect[I] = TOP;
      }
      else
      {
        if (I->getOpcode() == Instruction::Add)
        {
          effect[I] = std::make_pair(value1.first + value2.first, true);
        }
        else if (I->getOpcode() == Instruction::Sub)
        {
          effect[I] = std::make_pair(value1.first - value2.first, true);
        }
        else if (I->getOpcode() == Instruction::Mul)
        {
          effect[I] = std::make_pair(value1.first * value2.first, true);
        }
        else if (I->getOpcode() == Instruction::UDiv)
        {
          effect[I] = std::make_pair(static_cast<unsigned int>(value1.first / value2.first), true);
        }
        else if (I->getOpcode() == Instruction::SDiv)
        {
          effect[I] = std::make_pair(value1.first / value2.first, true);
        }
        else if (I->getOpcode() == Instruction::URem)
        {
          effect[I] = std::make_pair(static_cast<unsigned int>(value1.first % value2.first), true);
        }
        else if (I->getOpcode() == Instruction::SRem)
        {
          effect[I] = std::make_pair(value1.first % value2.first, true);
        }
        else if (I->getOpcode() == Instruction::Shl)
        {
          effect[I] = std::make_pair(value1.first << value2.first, true);
        }
        else if (I->getOpcode() == Instruction::LShr)
        {
          effect[I] = std::make_pair(value1.first >> static_cast<unsigned int>(value2.first), true);
        }
        else if (I->getOpcode() == Instruction::AShr)
        {
          effect[I] = std::make_pair(value1.first >> value2.first, true);
        }
        else if (I->getOpcode() == Instruction::And)
        {
          effect[I] = std::make_pair(value1.first & value2.first, true);
        }
        else if (I->getOpcode() == Instruction::Or)
        {
          effect[I] = std::make_pair(value1.first | value2.first, true);
        }
        else if (I->getOpcode() == Instruction::Xor)
        {
          effect[I] = std::make_pair(value1.first ^ value2.first, true);
        }
      }
    }
    else if (isa<LoadInst>(I))
    {
      effect[I] = effect[I->getOperand(0)];
    }
    else if (isa<StoreInst>(I))
    {
      op1 = I->getOperand(0);
      if (dyn_cast<Constant>(op1) == NULL)
      {
        if (effect.find(op1) == effect.end())
        {
          value1 = arguments[prev_instruction->getFunction()][op1];
        }
        else
        {
          value1 = effect[op1];
        }
      }
      else
      {
        value1 = std::make_pair(dyn_cast<Constant>(op1)->getUniqueInteger().getSExtValue(), true);
      }

      effect[I->getOperand(1)] = value1;
    }
    else if (isa<CallInst>(I))
    {
      F = dyn_cast<CallInst>(I)->getCalledFunction();

      if (F->getName() == "__isoc99_scanf")
      {
        for (Value *op : I->operands())
        {
          if (effect.find(op) != effect.end())
          {
            effect[op] = BOTTOM;
          }
        }
      }
      else if (F->getName() != "printf")
      {
        if (F->getReturnType()->isIntegerTy(32))
        {
          effect[I] = return_values[F];
        }

        for (Value *op : I->operands())
        {
          if (op->getType()->isIntegerTy(32))
          {
            if (dyn_cast<Constant>(op) == NULL)
            {
              actual_arguments[F->arg_begin() + std::distance(I->op_begin(), std::find(I->op_begin(), I->op_end(), op))] = effect[op];
            }
            else
            {
              actual_arguments[F->arg_begin() + std::distance(I->op_begin(), std::find(I->op_begin(), I->op_end(), op))] = std::make_pair(dyn_cast<Constant>(op)->getUniqueInteger().getSExtValue(), true);
            }
          }
        }

        old_arguments = arguments[F];
        arguments[F] = meet(old_arguments, actual_arguments);
        if (arguments[F] != old_arguments)
        {
          worklist.insert(F);
        }

        callers[F].insert(I->getFunction());
      }
    }
    else if (isa<ReturnInst>(I))
    {
      if (I->getFunction()->getReturnType()->isIntegerTy(32))
      {
        op1 = I->getOperand(0);
        if (dyn_cast<Constant>(op1) == NULL)
        {
          value1 = effect[op1];
        }
        else
        {
          value1 = std::make_pair(dyn_cast<Constant>(op1)->getUniqueInteger().getSExtValue(), true);
        }

        value2 = return_values[I->getFunction()];
        return_values[I->getFunction()] = meet(value2, value1);
        if (return_values[I->getFunction()] != value2)
        {
          for (Function *F : callers[I->getFunction()])
          {
            worklist.insert(F);
          }
        }
      }
    }
    else if (isa<PHINode>(I))
    {
      effect[I] = BOTTOM;
    }
    else if (isa<SelectInst>(I))
    {
      effect[I] = BOTTOM;
    }

    return effect;
  }

  void intraprocedural_constant_propagation(Function &F)
  {
    std::map<Value *, std::pair<int, bool>> initial_map, new_out;
    std::set <Instruction *> instruction_worklist;
    Instruction *I, *prev_instruction, *next_instruction;

    for (BasicBlock &BB : F)
    {
      for (Instruction &I : BB)
      {
        if (!isa<StoreInst>(I) && !isa<ICmpInst>(I) && !isa<BranchInst>(I) && !isa<ReturnInst>(I) && !isa<ZExtInst>(I))
        {
          initial_map[&I] = TOP;
        }
      }
    }

    for (BasicBlock &BB : F)
    {
      for (Instruction &I : BB)
      {
        out[&F][&I] = initial_map;
        instruction_worklist.insert(&I);
      }
    }

    while (!instruction_worklist.empty())
    {
      I = *instruction_worklist.begin();
      instruction_worklist.erase(I);
      prev_instruction = I->getPrevNode();
      if (prev_instruction || I == F.getEntryBlock().getFirstNonPHI())
      {
        new_out = calculate_effect(I, prev_instruction);
      }
      else
      {
        new_out = initial_map;
        for (BasicBlock *pred : predecessors(I->getParent()))
        {
          prev_instruction = pred->getTerminator();
          new_out = meet(new_out, calculate_effect(I, prev_instruction));
        }
      }

      if (new_out != out[&F][I])
      {
        out[&F][I] = new_out;
        next_instruction = I->getNextNode();

        if (next_instruction)
        {
          instruction_worklist.insert(next_instruction);
        }
        else
        {
          for (BasicBlock *succ : successors(I->getParent()))
          {
            next_instruction = succ->getFirstNonPHI();
            instruction_worklist.insert(next_instruction);
          }
        }
      }
    }
  }

  std::string getAsString(Value *V)
  {
    std::string s;
    raw_string_ostream rso(s);
    rso << *V;
    return rso.str();
  }

  std::string getNameOrAsOperand(Value *V)
  {
    std::string s;

    s = getAsString(V);

    return s.substr(s.find('%'), s.find_first_of(" ,)", s.find('%')) - s.find('%'));
  }

  bool runOnModule(Module &M) override
  {
    // It is assumed that the opt tool is run from the llvm-project/build/ folder

    Function *F;
    bool flag;

    for (auto &F : M)
    {
      if (F.getName() != "__isoc99_scanf" && F.getName() != "printf")
      {
        arguments[&F] = std::map<Value *, std::pair<int, bool>>();
        for (Argument &Arg : F.args())
        {
          if (Arg.getType()->isIntegerTy(32))
          {
            arguments[&F][&Arg] = TOP;
          }
        }

        if (F.getReturnType()->isIntegerTy(32))
        {
          return_values[&F] = TOP;
        }

        callers[&F] = std::set<Function *>();

        worklist.insert(&F);
      }
    }

    while (!worklist.empty())
    {
      F = *worklist.begin();
      worklist.erase(F);
      intraprocedural_constant_propagation(*F);
    }

    for (auto &F : M)
    {
      if (F.getName() != "__isoc99_scanf" && F.getName() != "printf")
      {
        outs() << F.getName() << "(";

        for (auto &pair : arguments[&F])
        {
          if (pair.second == TOP)
          {
            outs() << "TOP";
          }
          else if (pair.second == BOTTOM)
          {
            outs() << "BOTTOM";
          }
          else
          {
            outs() << pair.second.first;
          }

          if (pair.first != arguments[&F].rbegin()->first)
          {
            outs() << ", ";
          }
        }

        outs() << ")";

        if (F.getReturnType()->isIntegerTy(32))
        {
          if (return_values[&F] == TOP)
          {
            outs() << " -> " << "TOP";
          }
          else if (return_values[&F] == BOTTOM)
          {
            outs() << " -> " << "BOTTOM";
          }
          else
          {
            outs() << " -> " << return_values[&F].first;
          }
        }

        outs() << "\n";
      }
    }

    for (auto &F : M)
    {
      for (auto &pair : arguments[&F])
      {
        if (pair.second.second == true)
        {
          pair.first->replaceAllUsesWith(ConstantInt::get(Type::getInt32Ty(M.getContext()), pair.second.first));
        }
      }

      for (auto &BB : F)
      {
        for (auto I = BB.begin(); I != BB.end();)
        {
          flag = false;
          if (I->getType()->isIntegerTy(32))
          {
            if (out[&F][&*I][&*I].second == true)
            {
              I->replaceAllUsesWith(ConstantInt::get(Type::getInt32Ty(M.getContext()), out[&F][&*I][&*I].first));
              if (!isa<CallInst>(I))
              {
                I = BB.getInstList().erase(I);
                flag = true;
              }
            }
          }
          
          if (!flag)
          {
            I++;
          }
        }
      }
    }

    for (auto &F : M)
    {
      for (auto &BB : F)
      {
        for (auto I = BB.begin(); I != BB.end();)
        {
          flag = false;
          if (isa<StoreInst>(I))
          {
            if (I->getOperand(1)->getNumUses() == 1)
            {
              I = BB.getInstList().erase(I);
              flag = true;
            }
          }
          
          if (!flag)
          {
            I++;
          }
        }
      }
    }

    for (auto &F : M)
    {
      for (auto &BB : F)
      {
        for (auto I = BB.begin(); I != BB.end();)
        {
          flag = false;
          if (isa<AllocaInst>(I))
          {
            if (I->getNumUses() == 0)
            {
              I = BB.getInstList().erase(I);
              flag = true;
            }
          }
          
          if (!flag)
          {
            I++;
          }
        }
      }
    }

    return true;
  }

  // bool runOnFunction(Function &F) override {
  //   // write your code here

  //   return false;
  // }
}; // end of struct cons_eval
}  // end of anonymous namespace

char cons_eval::ID = 0;
static RegisterPass<cons_eval> X("cons_eval_given", "Constant Propagation Pass for Assignment");
