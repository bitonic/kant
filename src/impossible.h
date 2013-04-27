#ifndef _IMPOSSIBLE_H
#define _IMPOSSIBLE_H
#define IMPOSSIBLE(err) (error ("Error at file " ++ __FILE__ ++ ", line " ++ show (__LINE__ :: Integer) ++ ":\n" ++ (err)))
#endif
