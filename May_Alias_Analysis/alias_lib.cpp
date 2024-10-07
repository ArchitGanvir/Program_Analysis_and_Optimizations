#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/IR/LegacyPassManager.h"

#include <fstream>
#include "llvm/IR/Instructions.h"
#include <algorithm>
#include <iterator>
#include "llvm/IR/Module.h"

using namespace llvm;

namespace {
struct alias_c : public FunctionPass {
  static char ID;
  alias_c() : FunctionPass(ID) {}

  // Checks if the given variable has a name or not
  bool hasName(std::string s)
  {
    if (s[0] == '%' || s.compare(0, 10, "arraydecay") == 0)
    {
      return false;
    }

    return true;
  }

  bool runOnFunction(Function &F) override {
    // The -fno-discard-value-names flag has been used while using clang to generate the LLVM IR files (to preserve the variable names)
    // It is assumed that the opt tool is run from the llvm-project/build/ folder

    int num_instructions = 0, i, flag, instruction_number, prev_instruction_number, j, next_instruction_number;

    std::vector<std::pair<std::string, std::set<std::string>>> initial_points_to_map, alias_map;

    std::string instruction_statement, local_identifier, ptr1, ptr2, input_filepath, output_filename, pointer_name;

    Instruction *prev_instruction;

    BasicBlock *successor;

    std::set<std::string> intersect;

    std::ofstream output_file;

    const std::string output_directory_path = "../assignment-3-may-alias-analysis-ArchitGanvir/output/";

    for (BasicBlock &BB : F)  // Counting the number of instructions in the function
    {
      num_instructions += BB.size();
    }

    bool worklist[num_instructions];

    std::vector<std::pair<std::string, std::set<std::string>>> out[num_instructions], new_out[num_instructions];

    // Calculating the initial values for the points-to maps and initializing alias_map

    for (auto &B : F) // Getting the pointers from the instruction statements
    {
      for (auto &I : B)
      {
        if (AllocaInst *AI = dyn_cast<AllocaInst>(&I))
        {
          if (AI->getAllocatedType()->isPointerTy()) // Variables assigned in alloca instructions are always named
          {
            initial_points_to_map.push_back(std::make_pair(std::string(AI->getName()), std::set<std::string>{}));
            alias_map.push_back(std::make_pair(std::string(AI->getName()), std::set<std::string>{}));
          }
          else if (AI->getAllocatedType()->isArrayTy())
          {
            initial_points_to_map.push_back(std::make_pair(std::string(AI->getName()), std::set<std::string>{std::string(AI->getName()) + "[0]"}));
            alias_map.push_back(std::make_pair(std::string(AI->getName()), std::set<std::string>{}));
          }
        }
        else if (LoadInst *LI = dyn_cast<LoadInst>(&I))
        {
          if (LI->getType()->isPointerTy()) // Variables assigned in load instructions are always unnamed
          {
            std::string s;  // Getting the instruction statement as a string
            raw_string_ostream rso(s);
            rso << I;
            instruction_statement = rso.str();

            local_identifier = instruction_statement.substr(instruction_statement.find("%"), instruction_statement.find(" ", instruction_statement.find("%")) - instruction_statement.find("%"));  // Getting the local identifier which is being assigned

            initial_points_to_map.push_back(std::make_pair(local_identifier, std::set<std::string>{}));
          }
        }
        else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(&I))  // Variables assigned in getelementptr instructions are treated as unnamed
        {
          initial_points_to_map.push_back(std::make_pair(std::string(GEP->getName()), std::set<std::string>{}));
        }
      }
    }

    for (i = 0; i < num_instructions; i++)  // Initializing the worklist and OUT maps
    {
      worklist[i] = true;  // Adding all the instructions to the worklist

      out[i] = initial_points_to_map;
    }

    while (1) // Performing the may-alias analysis
    {
      for (i = 0; i < num_instructions; i++)  // Checking if the worklist is empty
      {
        if (worklist[i] == true)
        {
          break;
        }
      }

      if (i == num_instructions)
      {
        break;
      }
      
      worklist[i] = false;  // Removing the instruction from the worklist

      instruction_number = 0;

      new_out[i] = initial_points_to_map; // Initializing the new OUT map

      flag = 0; // For checking if the instruction has been found
      for (BasicBlock &BB : F)
      {
        for (Instruction &I : BB)
        {
          if (i == instruction_number)
          {
            flag = 1; // The instruction has been found

            prev_instruction = I.getPrevNode();

            // Calculating the IN map

            if (prev_instruction != NULL) // Checking if the instruction is not the first instruction in its basic block
            {
              prev_instruction_number = i - 1;

              new_out[i] = out[prev_instruction_number]; // Copying the OUT map of the previous instruction into the new OUT map
            }
            else
            {
              prev_instruction_number = -1; // For finding the last instruction of a predecessor basic block
              for (BasicBlock &BB_ : F)
              {
                prev_instruction_number += BB_.size();

                for (j = 0; j < BB_.getTerminator()->getNumSuccessors(); j++)
                {
                  if (BB_.getTerminator()->getSuccessor(j) == &BB)  // Checking if BB_is a predecessor of BB
                  {
                    // Assigning the union of the new OUT map and the OUT map of BB_ to the new OUT map

                    for (auto &pair : new_out[i])
                    {
                      for (auto &other_pair : out[prev_instruction_number])
                      {
                        if (pair.first == other_pair.first)
                        {
                          pair.second.insert(other_pair.second.begin(), other_pair.second.end());

                          break;
                        }
                      }
                    }
                  }
                }
              }
            }

            std::string s;  // Getting the instruction statement as a string
            raw_string_ostream rso(s);
            rso << I;
            instruction_statement = rso.str();

            // Calculating the new OUT map

            if (LoadInst *LI = dyn_cast<LoadInst>(&I))
            {
              if (LI->getType()->isPointerTy())
              {
                ptr1 = instruction_statement.substr(instruction_statement.find("%"), instruction_statement.find(" ", instruction_statement.find("%")) - instruction_statement.find("%"));  // Getting the local identifier which is being assigned

                ptr2 = std::string(LI->getOperand(0)->getName());  // Getting the pointer operand

                if (ptr2.empty())
                {
                  ptr2 = instruction_statement.substr(instruction_statement.find_last_of('%'), instruction_statement.find_last_of(',') - instruction_statement.find_last_of('%'));
                }

                if (hasName(ptr2))
                {
                  for (auto &pair : new_out[i])
                  {
                    if (pair.first == ptr1)
                    {
                      for (auto &other_pair : new_out[i])
                      {
                        if (other_pair.first == ptr2)
                        {
                          pair.second = other_pair.second;

                          break;
                        }
                      }

                      break;
                    }
                  }
                }
                else
                {
                  for (auto &pair : new_out[i])
                  {
                    if (pair.first == ptr1)
                    {
                      pair.second.clear();

                      for (auto &other_pair : new_out[i])
                      {
                        if (other_pair.first == ptr2)
                        {
                          for (auto &ptr : other_pair.second)
                          {
                            for (auto &another_pair : new_out[i])
                            {
                              if (another_pair.first == ptr)
                              {
                                pair.second.insert(another_pair.second.begin(), another_pair.second.end());

                                break;
                              }
                            }
                          }

                          break;
                        }
                      }

                      break;
                    }
                  }
                }
              } 
            }
            else if (StoreInst *SI = dyn_cast<StoreInst>(&I))
            {
              if (SI->getOperand(0)->getType()->isPointerTy())
              {
                ptr1 = std::string(SI->getOperand(0)->getName());  // Getting the value operand

                if (ptr1.empty()) // Checking if the value operand is unnamed
                {
                  ptr1 = instruction_statement.substr(instruction_statement.find('%'), instruction_statement.find(',') - instruction_statement.find('%')); // Getting the value operand from the instruction statement
                }
                
                ptr2 = std::string(SI->getOperand(1)->getName());  // Getting the pointer operand

                if (ptr2.empty()) // Checking if the pointer operand is unnamed
                {
                  ptr2 = instruction_statement.substr(instruction_statement.find_last_of('%'), instruction_statement.find_last_of(',') - instruction_statement.find_last_of('%')); // Getting the pointer operand from the instruction statement
                }

                if (hasName(ptr1) && hasName(ptr2))
                {
                  for (auto &pair : new_out[i])
                  {
                    if (pair.first == ptr2)
                    {
                      pair.second.clear();
  
                      pair.second.insert(ptr1);
  
                      break;
                    }
                  }
                }
                else if (hasName(ptr1))
                {
                  for (auto &pair : new_out[i])
                  {
                    if (pair.first == ptr2)
                    {
                      if (pair.second.size() == 1)
                      {
                        for (auto &other_pair : new_out[i])
                        {
                          if (other_pair.first == *pair.second.begin())
                          {
                            other_pair.second.clear();

                            other_pair.second.insert(ptr1);

                            break;
                          }
                        }
                      }
                      else
                      {
                        for (auto &ptr : pair.second)
                        {
                          for (auto &other_pair : new_out[i])
                          {
                            if (other_pair.first == ptr)
                            {
                              other_pair.second.insert(ptr1);

                              break;
                            }
                          }
                        }
                      }

                      break;
                    }
                  }
                }
                else if (hasName(ptr2))
                {
                  for (auto &pair : new_out[i])
                  {
                    if (pair.first == ptr2)
                    {
                      for (auto &other_pair : new_out[i])
                      {
                        if (other_pair.first == ptr1)
                        {
                          pair.second = other_pair.second;

                          break;
                        }
                      }

                      break;
                    }
                  }
                }
                else
                {
                  for (auto &pair : new_out[i])
                  {
                    if (pair.first == ptr2)
                    {
                      if (pair.second.size() == 1)
                      {
                        for (auto &other_pair : new_out[i])
                        {
                          if (other_pair.first == *pair.second.begin())
                          {
                            other_pair.second.clear();

                            for (auto &another_pair : new_out[i])
                            {
                              if (another_pair.first == ptr1)
                              {
                                other_pair.second = another_pair.second;

                                break;
                              }
                            }

                            break;
                          }
                        }
                      }
                      else
                      {
                        for (auto &ptr : pair.second)
                        {
                          for (auto &other_pair : new_out[i])
                          {
                            if (other_pair.first == ptr)
                            {
                              for (auto &another_pair : new_out[i])
                              {
                                if (another_pair.first == ptr1)
                                {
                                  other_pair.second.insert(another_pair.second.begin(), another_pair.second.end());

                                  break;
                                }
                              }

                              break;
                            }
                          }
                        }
                      }

                      break;
                    }
                  }
                }
              }
            }
            else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(&I))
            {
              ptr1 = std::string(GEP->getName());

              ptr2 = std::string(GEP->getPointerOperand()->getName());

              for (auto &pair : new_out[i])
              {
                if (pair.first == ptr1)
                {
                  for (auto &other_pair : new_out[i])
                  {
                    if (other_pair.first == ptr2)
                    {
                      pair.second = other_pair.second;

                      break;
                    }
                  }
                  
                  break;
                }
              }
            }

            if (out[i] == new_out[i]) // Checking if the old OUT map is equal to the new OUT map
            {
              break;
            }

            out[i] = new_out[i]; // Copying the new OUT map into the old OUT map

            // Adding all the successors of the instruction to the worklist

            if (I.getNextNode() != NULL) // Checking if the instruction is not the last instruction in its basic block
            {
              worklist[i + 1] = true; // Adding the next instruction to the worklist
            }
            else
            {
              for (j = 0; j < I.getNumSuccessors(); j++)  // Adding the first instruction of all successor basic blocks to the worklist
              {
                successor = I.getSuccessor(j);
                next_instruction_number = 0; // For finding the instruction number of the first instruction of the successor basic block
                for (BasicBlock &BB : F)  // Iterating through all the basic blocks to find the successor basic block
                {
                  if (&BB == successor) // Checking if the basic block is a successor basic block
                  {
                    worklist[next_instruction_number] = true;  // Adding the first instruction of the successor basic block to the worklist

                    break;
                  }

                  next_instruction_number += BB.size();  // Counting the number of instructions that come before the first instruction of the successor basic block
                }
              } 
            }

            break;
          }

          instruction_number++;
        }

        if (flag == 1)  // Checking if the instruction had been found
        {
          break;
        }
      }
    }

    // Calculating alias_map

    for (i = num_instructions - 1; i < num_instructions; i++)  // Checking the OUT map of each instruction
    {
      for (auto &pair : out[i])
      {
        if (hasName(pair.first))
        {
          for (auto &other_pair : out[i])
          {
            if (hasName(other_pair.first) && pair.first != other_pair.first)
            {
              flag = 0; // For checking if the pair is already present in alias_map
              for (auto &alias_pair : alias_map)
              {
                if (alias_pair.first == pair.first)
                {
                  if (alias_pair.second.find(other_pair.first) != alias_pair.second.end())
                  {
                    flag = 1; // The pair is already present in alias_map

                    break;
                  }
                }
              }

              if (flag == 0)  // If the pair is not already present in alias_map
              {
                intersect.clear();

                set_intersection(pair.second.begin(), pair.second.end(), other_pair.second.begin(), other_pair.second.end(), std::inserter(intersect, intersect.begin()));

                if (!intersect.empty())
                {
                  for (auto &alias_pair : alias_map)
                  {
                    if (alias_pair.first == pair.first)
                    {
                      alias_pair.second.insert(other_pair.first);
                    }
                  }
                }
              }
            }
          }
        }
      }
    }

    input_filepath = std::string(F.getParent()->getName()); // Getting the path to the input file

    output_filename = input_filepath.substr(input_filepath.find_last_of('/') + 1, input_filepath.find_last_of('.') - input_filepath.find_last_of('/') - 1) + ".txt";  // Getting the name of the output file

    if (F.getName() == F.getParent()->begin()->getName()) // Checking if the function is the first function in the module
    {
      output_file.open(output_directory_path + output_filename);  // Creating a new file or overwriting the existing file
    }
    else
    {
      output_file.open(output_directory_path + output_filename, std::ios_base::app);  // Appending to the existing file
    }

    // Printing the output

    output_file << std::string(F.getName()) << "\n"; // Printing the function name
    errs() << std::string(F.getName()) << "\n";

    for (auto &pair : alias_map)
    {
      pointer_name = pair.first;

      pointer_name = pointer_name.substr(0, pointer_name.find_last_of('.'));  // Removing the .addr from the pointer name

      output_file << pointer_name << " -> {";
      errs() << pointer_name << " -> {";

      if (!pair.second.empty())
      {
        for (auto alias = pair.second.begin(); alias != --pair.second.end(); alias++)
        {
          pointer_name = *alias;

          pointer_name = pointer_name.substr(0, pointer_name.find_last_of('.'));  // Removing the .addr from the pointer name

          output_file << pointer_name << ", ";
          errs() << pointer_name << ", ";
        }

        pointer_name = *pair.second.rbegin();

        pointer_name = pointer_name.substr(0, pointer_name.find_last_of('.'));  // Removing the .addr from the pointer name

        output_file << pointer_name;
        errs() << pointer_name;
      }

      output_file << "}\n";
      errs() << "}\n";
    }

    output_file.close();

    return false;
  }
}; // end of struct alias_c
}  // end of anonymous namespace

char alias_c::ID = 0;
static RegisterPass<alias_c> X("alias_lib_given", "Alias Analysis Pass for Assignment",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);
