/*++
Copyright (c) 2007 Microsoft Corporation

Module Name:

    z3.h

Abstract:

    Z3 API.

Author:

    Nikolaj Bjorner (nbjorner)
    Leonardo de Moura (leonardo) 2007-06-8

Notes:

--*/

#pragma once

#include <stdbool.h>
#include <stdint.h>
#include "z3_macros.h"
#include "z3_api.h"
#include "z3_ast_containers.h"
#include "z3_algebraic.h"
#include "z3_polynomial.h"
#include "z3_rcf.h"
#include "z3_fixedpoint.h"
#include "z3_optimization.h"
#include "z3_fpa.h"
#include "z3_spacer.h"

inline void Z3_API Z3_set_error_handler_b(Z3_context c, void (*handle) (Z3_context c, Z3_error_code e)) {
  Z3_set_error_handler(c, handle);
}
