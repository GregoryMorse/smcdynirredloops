# as --32 -al=selfmodmodel32.lst selfmodmodelgas.asm
# as --64 -al=selfmodmodel64.lst -defsym rax=1 selfmodmodelgas.asm

.intel_syntax noprefix
.text

.IFDEF rax

#blueprint proc
        nodeaddrloc:
        mov rax, 0xFFFFFFFFFFFFFFFF # mov rax, imm64=48/ b8 <imm64>
        # 16 byte alignment needed for calling back into C code, but call from C plus call to blueprint is realigned
        # 32 not needed for shadow space as C-prototype compatibility is not needed
        mov rcx, 0xFFFFFFFFFFFFFFFF # mov rcx, imm64=48/ b9 <imm64> # index %indexoffs%2%
        mov rax, [rcx]
        mov qword ptr [nodeaddrloc+(nodeaddrloc+1+1-$-7)], rax
        mov qword ptr [nodeaddrloc+(lowlinkloc+1+1-$-7)], rax
        inc rax
        mov [rcx], rax
        peekretloc:
        pop rax # pop rax=58
        lea rsp, [rsp-8] # lea rsp, [rsp-8]=48/ 8D 64 24 F8
        mov qword ptr [nodeaddrloc+(retloc+1+1-$-7)], rax
        mov qword ptr [nodeaddrloc+(onstackloc+1+1-$-7)], rsp
        mov qword ptr [nodeaddrloc+(topopstackloc+1+1-$-7)], rsp
        mov dword ptr [nodeaddrloc+(nodeaddrloc+1+1+8-$-(1+1+4+4))], 0x900008c2 # c3=ret/retn ret 8=C2 0008
        counterloc:
        mov rax, 0xFFFFFFFFFFFFFFFF # mov rax, imm64=48/ b8 <imm64> # succ[x].size() %counteroffs%2%
        cmp rax, 0
        jz onstackloc
        dec rax
        mov qword ptr [nodeaddrloc+(counterloc+1+1-$-7)], rax
        mov rdx, rax
        mov rcx, 0xFFFFFFFFFFFFFFFF # getsuccnodeaddr/std::function<void*(int)> %getsuccnodeaddroffs%2%
        mov rax, 0xFFFFFFFFFFFFFFFF # std::function<void*(int)>::operator() %getsuccnodeaddroppoffs%2%
        lea rsp, [rsp-32] # shadow space
        call rax
        lea rsp, [rsp+32]
        .byte 0xC6, 0x40, 0x30, 0x08 # mov byte ptr [rax+(peekretloc+1+1+1+1+1-nodeaddrloc)], 08h # lea rsp, [rsp+8]=48/ 8D 64 24 08
        .byte 0x81, 0x78, 0x0A, 0xc2, 0x08, 0x00, 0x90 # cmp dword ptr [rax+(nodeaddrloc+1+1+8-nodeaddrloc)], 0x900008c2
        jz topopstackloc
        mov dword ptr [rax+(retlocadd-nodeaddrloc)], 0x909003EB # nop nop nop nop nop=90 90 90 90 90 or jmp $+3=EB 03 90 90 90
        topopstackloc:
        mov rcx, 0xFFFFFFFFFFFFFFFF # mov rcx, imm64=48/ b9 <imm64>
        cmp rcx, rsp
        jnz callloc
        .byte 0xC7, 0x40, 0x2C, 0x48, 0x8b, 0x04, 0x24 # mov dword ptr [rax+(peekretloc+1-nodeaddrloc)], 024048B48h # mov rax, [rsp] = 48/ 8B 04 24
        .byte 0xC6, 0x40, 0x2B, 0x90 # mov byte ptr [rax+(peekretloc-nodeaddrloc)], 90h
        .byte 0xC6, 0x40, 0x30, 0x90 # mov byte ptr [rax+(peekretloc+1+1+1+1+1-nodeaddrloc)], 90h
        callloc:
        lea rsp, [rsp-8]
        call rax
        calllocp1:
        cmp rax, qword ptr [nodeaddrloc+(lowlinkloc+1+1-$-7)]
        jge counterloc
        mov qword ptr [nodeaddrloc+(lowlinkloc+1+1-$-7)], rax
        mov ecx, ((lowlinkloc-(checksccloc+2)) SHL 8) OR 0xeb
        # mov ecx, <imm32>=B9 <imm32>
        # mov cx, <imm16>=66| B9 <imm16>
        # db 066h, 0b9h
        # dw ((lowlinkloc-(checksccloc+2)) SHL 8) OR 0ebh
        mov word ptr [nodeaddrloc+(checksccloc-$-7)], cx # relative jmp=eb <disp8>
        jmp counterloc
        onstackloc:
        mov rcx, 0xFFFFFFFFFFFFFFFF # mov rax, imm64=48/ b9 <imm64>
        cmp rcx, rsp
        jnz checksccloc
        lea rax, byte ptr [nodeaddrloc+(calllocp1-$-7)]
        lea rsp, [rsp-8]
        push rax
        checksccloc:
        .byte 0x90, 0x90 # nop=90
        nextnodeloc:
        pop rax
        lea rsp, [rsp+8]
        sub rax, calllocp1-nodeaddrloc
        mov rdx, 0xFFFFFFFFFFFFFFFF # starttopo %starttopooffs%2%
        mov rcx, [rdx]
        add rax, nodeaddrsetloc-nodeaddrloc
        mov [rcx+1+1], rax
        inc rax
        inc rax
        lea rcx, byte ptr [nodeaddrloc+(nodeaddrloc-$-7)]
        mov [rax], rcx
        dec rax
        dec rax
        sub rax, nodeaddrsetloc-nodeaddrloc
        add rax, nexttopoloc-nodeaddrloc
        mov [rdx], rax
        sub rax, nexttopoloc-nodeaddrloc
        inc rax
        inc rax
        mov rdx, 0xFFFFFFFFFFFFFFFF # succ.size() %succsizeoffs%2%
        mov [rax], rdx
        dec rax
        dec rax
        cmp rcx, rax
        jnz nextnodeloc
        lowlinkloc:
        mov rax, 0xFFFFFFFFFFFFFFFF # mov rax, imm64=48/ b8 <imm64>
        retlocadd:
        lea rsp, [rsp+8] # lea rsp, [rsp+8]=48/ 8D 64 24 08
        retloc:
        mov rcx, 0xFFFFFFFFFFFFFFFF # mov rax, imm64=48/ b9 <imm64>
        jmp rcx
        nodeaddrsetloc:
        mov rax, 0xFFFFFFFFFFFFFFFF # mov rax, imm64=48/ b8 <imm64>
        cmp qword ptr [nodeaddrloc+(nodeaddrsetloc+1+1-$-7)], rax # nodeaddr[-x]+nodeaddrsetloc+1+1 %checksamesccoffs%3%
        jnz satloc
        mov rcx, 0xFFFFFFFFFFFFFFFF # mov rcx, imm64=48/ b9 <imm64> # unsat/std::function<void()> %unsatoffs%2%
        mov rax, 0xFFFFFFFFFFFFFFFF # std::function<void()>::operator() %unsatoppoffs%2%
        jmp rax
        satloc:
        mov rcx, 0
        lea rsp, [rsp-8-32] # 16-byte align and shadow space
        mov rcx, 0xFFFFFFFFFFFFFFFF # addsolution/std::function<void()> %addsolutionoffs%2%
        mov rax, 0xFFFFFFFFFFFFFFFF # std::function<void()>::operator() %addsolutionoppoffs%2%
        call rax
        lea rsp, [rsp+8+32]
        mov rcx, 0xFFFFFFFFFFFFFFFF # mov rcx, imm64=48/ b9 <imm64> ; sat/std::function<void()> %satoffs%2%
        nexttopoloc:
        mov rax, 0xFFFFFFFFFFFFFFFF # std::function<void()>::operator() %satoppoffs%2%
        jmp rax
#blueprint endp

#callblueprint proc
        mov rax, 0xFFFFFFFFFFFFFFFF # for each node %callblueprintoffs%2%
        cmp dword ptr [rax+(1+1+8)], 0x900008c2 # nodeaddrloc+1+1+8-nodeaddrloc
        jz dontcall
        call rax
        dontcall:
#callblueprint endp

#jumptopo proc
        mov rcx, 0xFFFFFFFFFFFFFFFF # mov rcx, imm64=48/ b9 <imm64> # sat %jumptopooffs%2%
        jmp rcx
#jumptopo endp

.ELSE

#blueprint proc
        nodeaddrloc:
        mov eax, 0xFFFFFFFF # mov eax, imm32=b8 <imm32>
        mov ecx, 0xFFFFFFFF # mov ecx, imm32=b9 <imm32> # index %indexoffs%1%
        mov eax, [ecx]
        mov dword ptr [nodeaddrloc+(nodeaddrloc+1-$-5)], eax # fixup %fixup1%1%
        mov dword ptr [nodeaddrloc+(lowlinkloc+1-$-5)], eax # fixup %fixup2%1%
        inc eax
        mov [ecx], eax
        mov eax, [esp]
        peekretloc:
        pop eax # pop eax=58
        mov dword ptr [nodeaddrloc+(retloc+1-$-5)], eax # fixup %fixup3%1%
        mov dword ptr [nodeaddrloc+(onstackloc+1-$-6)], esp # fixup %fixup4%2%
        mov dword ptr [nodeaddrloc+(topopstackloc+1-$-6)], esp # fixup %fixup5%2%
        mov byte ptr [nodeaddrloc+(nodeaddrloc+1+4-$-(1+1+4))], 0xc3 # (1+1+4+1) c3=ret fixup %fixup6%2%
        counterloc:
        mov eax, 0xFFFFFFFF # mov eax, imm32=b8 <imm32> # succ[x].size() %counteroffs%1%
        cmp eax, 0
        jz onstackloc
        dec eax
        mov dword ptr [nodeaddrloc+(counterloc+1-$-5)], eax # fixup %fixup7%1%
        push eax
        mov ecx, 0xFFFFFFFF # getsuccnodeaddr/std::function<void*(int)> %getsuccnodeaddroffs%1%
        mov eax, 0xFFFFFFFF # std::function<void*(int)>::operator() %getsuccnodeaddroppoffs%1%
        call eax
        # thiscall on GCC uses cdecl while Microsoft uses stdcall lea esp, [esp+4]
        topopstackloc:
        mov ecx, 0xFFFFFFFF # mov ecx, imm32=b9 <imm32>
        cmp ecx, esp
        jnz callloc
        mov byte ptr [eax+(peekretloc-nodeaddrloc)], 0x90 # mov eax, [esp] = 8B 04 24 nop=90
        callloc:
        call eax
        calllocp1:
        cmp eax, dword ptr [nodeaddrloc+(lowlinkloc+1-$-6)] # fixup %fixup8%2%
        jge counterloc
        mov dword ptr [nodeaddrloc+(lowlinkloc+1-$-5)], eax # fixup %fixup9%1%
        mov ecx, ((lowlinkloc-(checksccloc+2)) SHL 8) OR 0xeb
        # mov ecx, <imm32>=B9 <imm32>
        # mov cx, <imm16>=66| B9 <imm16>
        # db 066h, 0b9h
        # dw ((lowlinkloc-(checksccloc+2)) SHL 8) OR 0ebh
        mov word ptr [nodeaddrloc+(checksccloc-$-7)], cx # relative jmp=eb <disp8> fixup %fixup10%3%
        jmp counterloc
        onstackloc:
        mov ecx, 0xFFFFFFFF # mov eax, imm32=b9 <imm32>
        cmp ecx, esp
        jnz checksccloc
        lea eax, byte ptr [nodeaddrloc+(calllocp1-$-6)] # fixup %fixup11%2%
        push eax
        checksccloc:
        .byte 0x90, 0x90 # nop=90
        nextnodeloc:
        pop eax
        sub eax, calllocp1-nodeaddrloc
        mov edx, 0xFFFFFFFF # starttopo %starttopooffs%1%
        mov ecx, [edx]
        add eax, nodeaddrsetloc-nodeaddrloc
        mov [ecx+1], eax
        inc eax
        lea ecx, byte ptr [nodeaddrloc+(nodeaddrloc-$-6)] # fixup %fixup12%2%
        mov [eax], ecx
        dec eax
        sub eax, nodeaddrsetloc-nodeaddrloc
        add eax, nexttopoloc-nodeaddrloc
        mov [edx], eax
        sub eax, nexttopoloc-nodeaddrloc
        inc eax
        mov edx, 0xFFFFFFFF # succ.size() %succsizeoffs%1%
        mov [eax], edx
        dec eax
        cmp ecx, eax
        jnz nextnodeloc
        lowlinkloc:
        mov eax, 0xFFFFFFFF # mov eax, imm32=b8 <imm32>
        retloc:
        mov ecx, 0xFFFFFFFF # mov eax, imm32=b9 <imm32>
        jmp ecx
        nodeaddrsetloc:
        mov eax, 0xFFFFFFFF # mov eax, imm32=b8 <imm32>
        cmp dword ptr [nodeaddrloc+(nodeaddrsetloc+1-$-6)], eax # nodeaddr[-x]+nodeaddrsetloc+1 %checksamesccoffs%2%
        jnz satloc
        mov ecx, 0xFFFFFFFF # mov ecx, imm32=b9 <imm32> # unsat/std::function<void()> %unsatoffs%1%
        mov eax, 0xFFFFFFFF # std::function<void()>::operator() %unsatoppoffs%1%
        jmp eax
        satloc:
        mov ecx, 0
        mov ecx, 0xFFFFFFFF # addsolution/std::function<void()> %addsolutionoffs%1%
        mov eax, 0xFFFFFFFF # std::function<void()>::operator() %addsolutionoppoffs%1%
        call eax
        mov ecx, 0xFFFFFFFF # mov ecx, imm32=b9 <imm32> ; sat/std::function<void()> %satoffs%1%
        nexttopoloc:
        mov eax, 0xFFFFFFFF # std::function<void()>::operator() %satoppoffs%1%
        jmp eax
#blueprint endp

#callblueprint proc
        mov eax, 0xFFFFFFFF # for each node %callblueprintoffs%1%
        call eax
#callblueprint endp

#jumptopo proc
        mov ecx, 0xFFFFFFFF # mov ecx, imm32=b9 <imm32> # sat %jumptopooffs%1%
        jmp ecx
#jumptopo endp

.ENDIF