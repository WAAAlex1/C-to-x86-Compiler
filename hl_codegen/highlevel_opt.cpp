// Copyright (c) 2021-2023, David H. Hovemeyer <david.hovemeyer@gmail.com>
//
// Permission is hereby granted, free of charge, to any person obtaining a
// copy of this software and associated documentation files (the "Software"),
// to deal in the Software without restriction, including without limitation
// the rights to use, copy, modify, merge, publish, distribute, sublicense,
// and/or sell copies of the Software, and to permit persons to whom the
// Software is furnished to do so, subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included
// in all copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL
// THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR
// OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE,
// ARISING FROM, OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR
// OTHER DEALINGS IN THE SOFTWARE.

#include "highlevel_opt.h"
#include "cfg_builder.h"
#include "cfg_transform.h"

HighLevelOpt::HighLevelOpt(const Options &options)
  : m_options(options) {
}

HighLevelOpt::~HighLevelOpt() {
}

void HighLevelOpt::optimize(std::shared_ptr<Function> function) {
  assert(m_options.has_option(Options::OPTIMIZE));

  // m_function can be used by helper functions to refer to
  // the Function
  m_function = function;

  std::shared_ptr<InstructionSequence> hl_iseq = m_function->get_hl_iseq();
  auto hl_cfg_builder = ::make_highlevel_cfg_builder(hl_iseq);
  std::shared_ptr<ControlFlowGraph> hl_cfg = hl_cfg_builder.build();


  for(auto i = 2; i <= 2; i++) {
    LVNOptimization opt1(hl_cfg);                   // LOCAL VALUE NUMBERING OPTIMIZATION
    hl_cfg = opt1.transform_cfg();

    CPOptimization opt2(hl_cfg);                    // COPY PROPAGATION OPTIMIZATION
    hl_cfg = opt2.transform_cfg();

    DSOptimization opt3(hl_cfg);                    // DEAD STORE OPTIMIZATION (USES LIVENESS ANALYSIS)
    hl_cfg = opt3.transform_cfg();
  }

  LRAOptimization opt4(hl_cfg, m_function);         // LRA OPTIMIZATION (USES LIVENESS ANALYSIS)
  hl_cfg = opt4.transform_cfg();
  m_function->set_total_spilled_storage(opt4.get_spilledStorage());

  hl_iseq = hl_cfg->create_instruction_sequence();
  m_function->set_hl_iseq(hl_iseq);

}
