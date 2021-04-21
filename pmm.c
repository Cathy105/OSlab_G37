#include <defs.h>
#include <x86.h>
#include <stdio.h>
#include <string.h>
#include <mmu.h>
#include <memlayout.h>
#include <pmm.h>
#include <default_pmm.h>
#include <sync.h>
#include <error.h>

/* *
 * Task State Segment:
 *任务状态段：
   任务状态段可以在内存的任何位置出现。
   称为 任务寄存器（TR）的特殊段寄存器 包含 指向有效 任务状态段（TSS）的 段选择器
   该段选择器指向 驻留在GDT中的 有效TSS段描述符
   因此，使用TSS必须在函数gdt_init()中执行以下操作：
     1）在GDT中创建TSS描述符条目
     2）根据需要向内存中的TSS添加足够的信息
     3）用该段的段选择器加载TR寄存器
   TSS中有几个文件用于 在发生权限级别更改时 指定新的堆栈指针。
   但是在我们的操作系统内核中只有SS0和ESP0字段是有用的。
   字段SS0包含CPL=0的堆栈段选择器，字段ESP0包含CPL=0的新ESP值。
   在保护模式下发生中断时，x86 CPU将在TSS中查找SS0和ESP0，并将其值分别加载到SS和ESP中。
 * The TSS may reside anywhere in memory.
 * A special segment register called the Task Register (TR) holds a segment selector that points a valid TSS
 * segment descriptor which resides in the GDT. 
 * Therefore, to use a TSS 
 * the following must be done in function gdt_init:
 *   - create a TSS descriptor entry in GDT
 *   - add enough information to the TSS in memory as needed
 *   - load the TR register with a segment selector for that segment
 *
 * There are several fileds in TSS for specifying the new stack pointer when a privilege level change happens. 
 * But only the fields SS0 and ESP0 are useful in our os kernel.
 * The field SS0 contains the stack segment selector for CPL = 0, 
 * and the ESP0 contains the new ESP value for CPL = 0. 
 * When an interrupt happens in protected mode, the x86 CPU will look in the TSS for SS0 and ESP0 and load their value into SS and ESP respectively.
 * */
static struct taskstate ts = {0};

//物理调用页数组的虚拟地址
struct Page *pages;

//物理内存的数量（页）
size_t npage = 0;

//启动时页目录的虚拟地址
extern pde_t __boot_pgdir;
pde_t *boot_pgdir = &__boot_pgdir;

//启动时页目录的物理地址
//在X86系统中，页目录表的起始物理地址存放在cr3 寄存器中， 这个地址必须是一个页对齐的地址，也就是低 12 位必须为0。
uintptr_t boot_cr3;

//物理内存管理 
const struct pmm_manager *pmm_manager;

/* *
 * The page directory entry corresponding to the virtual address range [VPT, VPT + PTSIZE) points to the page directory itself. 
 Thus, the page directory is treated as a page table as well as a page directory.
 *
 * One result of treating the page directory as a page table is that all PTEs can be accessed though a "virtual page table" at virtual address VPT. 
 And the PTE for number n is stored in vpt[n].
 *
 * A second consequence is that the contents of the current page directory will always available at virtual address PGADDR(PDX(VPT), PDX(VPT), 0), to which vpd is set bellow.
  
  PTE(Page Table Entry)页表
  PDE(Page Directory Entry)页目录表
  与虚拟地址范围[VPT，VPT+PTSIZE）对应的页目录条目指向页目录本身。
  因此，页目录被视为页表和页目录。
  将页目录视为页表的一个结果是，可以通过虚拟地址VPT处的“虚拟页表”访问所有pte。
  数字n的PTE存储在vpt[n]中。
  第二个结果是当前页目录的内容将始终在虚拟地址PGADDR（PDX（VPT），PDX（VPT），0）处可用，vpd设置如下。
 
 * */
pte_t * const vpt = (pte_t *)VPT;
pde_t * const vpd = (pde_t *)PGADDR(PDX(VPT), PDX(VPT), 0);

/* *
 * Global Descriptor Table:
 *
 * The kernel and user segments are identical (except for the DPL). 
   To load the %ss register, the CPL must equal the DPL. 
   Thus, we must duplicate the segments for the user and the kernel. 
   Defined as follows:
 *   - 0x0 :  unused (always faults -- for trapping NULL far pointers)
 *   - 0x8 :  kernel code segment
 *   - 0x10:  kernel data segment
 *   - 0x18:  user code segment
 *   - 0x20:  user data segment
 *   - 0x28:  defined for tss, initialized in gdt_init
 全局描述符表：
内核和用户段是相同的（除了DPL）。
要加载%ss寄存器，CPL必须等于DPL(当前特权级必须等于所需要的特权级)。
因此，我们必须为用户和内核复制段。
定义如下：
-0x0:未使用（总是false--用于捕获空远指针）
-0x8：内核代码段
-0x10：内核数据段
-0x18：用户代码段
-0x20：用户数据段
-0x28:为tss定义，在gdt\u init中初始化
 * */
static struct segdesc gdt[] = {
    SEG_NULL,
    [SEG_KTEXT] = SEG(STA_X | STA_R, 0x0, 0xFFFFFFFF, DPL_KERNEL),
    [SEG_KDATA] = SEG(STA_W, 0x0, 0xFFFFFFFF, DPL_KERNEL),
    [SEG_UTEXT] = SEG(STA_X | STA_R, 0x0, 0xFFFFFFFF, DPL_USER),
    [SEG_UDATA] = SEG(STA_W, 0x0, 0xFFFFFFFF, DPL_USER),
    [SEG_TSS]   = SEG_NULL,
};

//伪描述符
static struct pseudodesc gdt_pd = {
    sizeof(gdt) - 1, (uintptr_t)gdt
};

static void check_alloc_page(void);
static void check_pgdir(void);
static void check_boot_pgdir(void);

/* *
 * lgdt - load the global descriptor table register and reset the data/code segement registers for kernel.
   lgdt—加载全局描述符表寄存器并重置内核态的数据/代码段寄存器。
 * */
static inline void
lgdt(struct pseudodesc *pd) {
    asm volatile ("lgdt (%0)" :: "r" (pd));
    asm volatile ("movw %%ax, %%gs" :: "a" (USER_DS));
    asm volatile ("movw %%ax, %%fs" :: "a" (USER_DS));
    asm volatile ("movw %%ax, %%es" :: "a" (KERNEL_DS));
    asm volatile ("movw %%ax, %%ds" :: "a" (KERNEL_DS));
    asm volatile ("movw %%ax, %%ss" :: "a" (KERNEL_DS));
    // reload cs
    asm volatile ("ljmp %0, $1f\n 1:\n" :: "i" (KERNEL_CS));
}

/* *
 * load_esp0 - change the ESP0 in default task state segment, so that we can use different kernel stack when we trap frame user to kernel.
   load_esp0-更改默认任务状态段中的esp0，以便在将帧用户捕获到内核时可以使用不同的内核堆栈。
 * */
void
load_esp0(uintptr_t esp0) {
    ts.ts_esp0 = esp0;
}

/* gdt_init - initialize the default GDT and TSS 
   gdt_init-初始化默认的gdt和TSS
*/
static void
gdt_init(void) {
    // set boot kernel stack and default SS0
    ////设置引导内核堆栈和默认SS0
    load_esp0((uintptr_t)bootstacktop);
    ts.ts_ss0 = KERNEL_DS;

    // initialize the TSS filed of the gdt
    //初始化gdt的TSS文件
    gdt[SEG_TSS] = SEGTSS(STS_T32A, (uintptr_t)&ts, sizeof(ts), DPL_KERNEL);

    // reload all segment registers
    //重新加载所有段寄存器
    lgdt(&gdt_pd);

    // load the TSS
    ltr(GD_TSS);
}

//init_pmm_manager - initialize a pmm_manager instance
//init_pmm_manager-初始化一个pmm_manager实例
static void
init_pmm_manager(void) {
    pmm_manager = &default_pmm_manager;
    cprintf("memory management: %s\n", pmm_manager->name);
    pmm_manager->init();
}

//init_memmap - call pmm->init_memmap to build Page struct for free memory
//init_memmap - 调用pmm->init_memmap为空闲内存构建页结构  
static void
init_memmap(struct Page *base, size_t n) {
    pmm_manager->init_memmap(base, n);
}

//alloc_pages - call pmm->alloc_pages to allocate a continuous n*PAGESIZE memory 
//alloc_pages - 调用pmm->alloc_pages来分配一个连续的n*PAGESIZE内存
struct Page *
alloc_pages(size_t n) {
    struct Page *page=NULL;
    bool intr_flag;
    local_intr_save(intr_flag);
    {
        page = pmm_manager->alloc_pages(n);
    }
    local_intr_restore(intr_flag);
    return page;
}

//free_pages - call pmm->free_pages to free a continuous n*PAGESIZE memory 
//释放内存
void
free_pages(struct Page *base, size_t n) {
    bool intr_flag;
    local_intr_save(intr_flag);
    {
        pmm_manager->free_pages(base, n);
    }
    local_intr_restore(intr_flag);
}

//nr_free_pages - call pmm->nr_free_pages to get the size (nr*PAGESIZE) of current free memory
//获取当前可用内存的大小（nr*PAGESIZE）
size_t
nr_free_pages(void) {
    size_t ret;
    bool intr_flag;
    local_intr_save(intr_flag);
    {
        ret = pmm_manager->nr_free_pages();
    }
    local_intr_restore(intr_flag);
    return ret;
}

/* pmm_init - initialize the physical memory management 
   初始化物理内存管理
*/
static void
page_init(void) {
    struct e820map *memmap = (struct e820map *)(0x8000 + KERNBASE);
    uint64_t maxpa = 0;

    cprintf("e820map:\n");
    int i;
    for (i = 0; i < memmap->nr_map; i ++) {
        uint64_t begin = memmap->map[i].addr, end = begin + memmap->map[i].size;
        cprintf("  memory: %08llx, [%08llx, %08llx], type = %d.\n",
                memmap->map[i].size, begin, end - 1, memmap->map[i].type);
        if (memmap->map[i].type == E820_ARM) {
            if (maxpa < end && begin < KMEMSIZE) {
                maxpa = end;
            }
        }
    }
    if (maxpa > KMEMSIZE) {
        maxpa = KMEMSIZE;
    }

    extern char end[];

    npage = maxpa / PGSIZE;
    pages = (struct Page *)ROUNDUP((void *)end, PGSIZE);

    for (i = 0; i < npage; i ++) {
        SetPageReserved(pages + i);
    }

    uintptr_t freemem = PADDR((uintptr_t)pages + sizeof(struct Page) * npage);

    for (i = 0; i < memmap->nr_map; i ++) {
        uint64_t begin = memmap->map[i].addr, end = begin + memmap->map[i].size;
        if (memmap->map[i].type == E820_ARM) {
            if (begin < freemem) {
                begin = freemem;
            }
            if (end > KMEMSIZE) {
                end = KMEMSIZE;
            }
            if (begin < end) {
                begin = ROUNDUP(begin, PGSIZE);
                end = ROUNDDOWN(end, PGSIZE);
                if (begin < end) {
                    init_memmap(pa2page(begin), (end - begin) / PGSIZE);
                }
            }
        }
    }
}

//boot_map_segment - setup&enable the paging mechanism
// parameters参数
//  la:   linear address of this memory need to map (after x86 segment map)
//  size: memory size
//  pa:   physical address of this memory
//  perm: permission of this memory  

//boot_map_segment-设置并启用分页机制
//la：需要映射的这个内存的线性地址（在x86段映射之后）
//size：内存大小
//pa：内存的物理地址
//perm：内存的权限

static void
boot_map_segment(pde_t *pgdir, uintptr_t la, size_t size, uintptr_t pa, uint32_t perm) {
    assert(PGOFF(la) == PGOFF(pa));
    size_t n = ROUNDUP(size + PGOFF(la), PGSIZE) / PGSIZE;
    la = ROUNDDOWN(la, PGSIZE);
    pa = ROUNDDOWN(pa, PGSIZE);
    for (; n > 0; n --, la += PGSIZE, pa += PGSIZE) {
        pte_t *ptep = get_pte(pgdir, la, 1);
        assert(ptep != NULL);
        *ptep = pa | PTE_P | perm;
    }
}


//boot_alloc_page-使用pmm->alloc_pages(1)分配一个页面
//返回值：此分配页的内核虚拟地址
//注意：此函数用于获取PDT（页目录表）和PT（页表）的内存
static void *
boot_alloc_page(void) {
    struct Page *p = alloc_page();
    if (p == NULL) {
        panic("boot_alloc_page failed.\n");
    }
    return page2kva(p);//page to kernel virtual address
}



//pmm_init-设置pmm来管理物理内存，构建PDT&PT来设置分页机制
//	  -检查pmm和页机制的正确性，打印PDT和PT 
void
pmm_init(void) {
    //我们已经启用了分页
    boot_cr3 = PADDR(boot_pgdir);

    //We need to alloc/free the physical memory (granularity is 4KB or other size). 
    //So a framework of physical memory manager (struct pmm_manager)is defined in pmm.h
    //First we should init a physical memory manager(pmm) based on the framework.
    //Then pmm can alloc/free the physical memory. 
    //Now the first_fit/best_fit/worst_fit/buddy_system pmm are available.
//我们需要分配/释放物理内存（粒度为4KB或其他大小）。
//因此，在pmm.h中定义了一个物理内存管理器框架（struct pmm_manager）
//首先，我们应该基于这个框架初始化一个物理内存管理器（pmm）。
//然后pmm可以分配/释放物理内存。
//现在提供了first_fit/best_fit/worst_fit/buddy_system pmm。
    init_pmm_manager();

    //检测物理内存空间，保留已用内存，
    //然后使用pmm->init_memmap创建释放页面列表
    page_init();

    //使用pmm->check验证pmm中alloc/free函数的正确性
    check_alloc_page();

    check_pgdir();

    static_assert(KERNBASE % PTSIZE == 0 && KERNTOP % PTSIZE == 0);


    //在自身中递归插入boot_pgdir,以在虚拟地址VPT处形成虚拟页表 
    boot_pgdir[PDX(VPT)] = PADDR(boot_pgdir) | PTE_P | PTE_W;


    //使用线性基地址 KERNBASE将所有物理内存映射到线性内存
    // linear_addr KERNBASE ~ KERNBASE + KMEMSIZE = phy_addr 0 ~ KMEMSIZE
    boot_map_segment(boot_pgdir, KERNBASE, KMEMSIZE, 0, PTE_W);


    // Since we are using bootloader's GDT,
    // we should reload gdt (second time, the last time) to get user segments and the TSS
    // map virtual_addr 0 ~ 4G = linear_addr 0 ~ 4G
    // then set kernel stack (ss:esp) in TSS, setup TSS in gdt, load TSS
    //因为我们使用的是引导加载程序的GDT，
    //我们应该重新加载gdt（第二次，最后一次）以获得用户段和TSS映射virtual_addr 0~4G= linear_addr 0~4G，
    //然后在TSS中设置内核态堆栈（ss:esp），在gdt中设置TSS，加载TSS
    gdt_init();

    //now the basic virtual memory map(see memalyout.h) is established.
    //check the correctness of the basic virtual memory map.
    //现在基本的虚拟内存映射（参见memalyout.h）已经建立。
    //检查基本虚拟内存映射的正确性。 
    check_boot_pgdir();

    print_pgdir();

}



//get_pte-get pte并为la返回此pte的内核虚拟地址
//-如果PT包含不存在的pte，请为PT分配一个页面
//参数：
//pgdir：PDT的内核虚拟基址
//la:需要映射的线性地址
//create：一个逻辑值，用于决定是否为PT分配一个页面
//return vaule：这个pte的内核虚拟地址 
pte_t *
get_pte(pde_t *pgdir, uintptr_t la, bool create) {
    /* LAB2 EXERCISE 2: YOUR CODE
     *
     * 如果你需要访问一个物理地址, 用 KADDR()
     * 有关一些宏，请阅读pmm.h
     *一些有用的宏和定义，您可以在下面的实现中使用它们。
     * MACROs or Functions:
     *   PDX(la) = 虚拟地址la的页目录项索引。
     *   KADDR(pa) : 获取物理地址并返回相应的内核虚拟地址。
     *   set_page_ref(page,1) : 表示该页被一次引用
     *   page2pa(page): 获取此（struct Page*）页 管理的内存的物理地址
     *   struct Page * alloc_page() : 页分配
     *   memset(void *s, char c, size_t n) : 将s指向的内存区域的前n个字节设置为指定值c。
     * DEFINEs:
     *   PTE_P           0x001                   // 页表/目录项标志位 : 存在Present
     *   PTE_W           0x002                   // 页表/目录项标志位 : 可写的
     *   PTE_U           0x004                   // 页表/目录项标志位 : 用户可以访问
     */
#if 0
    pde_t *pdep = NULL;   // (1) find page directory entry
    if (0) {              // (2) check if entry is not present
                          // (3) check if creating is needed, then alloc page for page table
                          // CAUTION: this page is used for page table, not for common data page
                          // (4) set page reference
        uintptr_t pa = 0; // (5) get linear address of page
                          // (6) clear page content using memset
                          // (7) set page directory entry's permission
    }
    return NULL;          // (8) return page table entry
#endif
//尝试获取页表，注：typedef uintptr_t pte_t;
//PDX:页目录索引 Page Directory Index
//la:线性地址 Linear Address
//PTX:页表索引 Page Table Index
    pde_t *pdep = &pgdir[PDX(la)]; // (1) find page directory entry
    //若获取不成功则执行下面的语句
    if (!(*pdep & PTE_P)) {
        struct Page *page;//申请一页
        if (!create || (page = alloc_page()) == NULL) {
            return NULL;
        }
        set_page_ref(page, 1);//引用次数需要加1
        uintptr_t pa = page2pa(page);//获取页的线性地址
        memset(KADDR(pa), 0, PGSIZE);
        *pdep = pa | PTE_U | PTE_W | PTE_P;//设置权限
    }
    return &((pte_t *)KADDR(PDE_ADDR(*pdep)))[PTX(la)];//返回页表地址
}

//get_page - 使用PDT pgdir获取线性地址la的相关页结构
struct Page *
get_page(pde_t *pgdir, uintptr_t la, pte_t **ptep_store) {
    pte_t *ptep = get_pte(pgdir, la, 0);
    if (ptep_store != NULL) {
        *ptep_store = ptep;
    }
    if (ptep != NULL && *ptep & PTE_P) {
        return pte2page(*ptep);
    }
    return NULL;
}

//page_remove_pte - 释放一个与线性地址la相关的页结构并清除和线性地址相关的PTE
//注：PT已更改，因此TLB需要失效
static inline void
page_remove_pte(pde_t *pgdir, uintptr_t la, pte_t *ptep) {
    /* LAB2 EXERCISE 3: YOUR CODE
     *
     * Please check if ptep is valid, and tlb must be manually updated if mapping is updated
     *
     * Maybe you want help comment, BELOW comments can help you finish the code
     *
     * Some Useful MACROs and DEFINEs, you can use them in below implementation.
     * MACROs or Functions:
     *   struct Page *page pte2page(*ptep): get the according page from the value of a ptep
     *   free_page : free a page
     *   page_ref_dec(page) : decrease page->ref. NOTICE: ff page->ref == 0 , then this page should be free.
     *   tlb_invalidate(pde_t *pgdir, uintptr_t la) : Invalidate a TLB entry, but only if the page tables being
     *                        edited are the ones currently in use by the processor.
     * DEFINEs:
     *   PTE_P           0x001                   // page table/directory entry flags bit : Present
     */
#if 0
    if (0) {                      //(1) check if page directory is present
        struct Page *page = NULL; //(2) find corresponding page to pte
                                  //(3) decrease page reference
                                  //(4) and free this page when page reference reachs 0
                                  //(5) clear second page table entry
                                  //(6) flush tlb
    }
#endif
    if (*ptep & PTE_P) {
        struct Page *page = pte2page(*ptep);
        if (page_ref_dec(page) == 0) {
            free_page(page);
        }
        *ptep = 0;
        tlb_invalidate(pgdir, la);
    }
}

//page_remove - free an Page which is related linear address la and has an validated pte
//释放一个与线性地址la相关并具有已验证的pte的页
void
page_remove(pde_t *pgdir, uintptr_t la) {
    pte_t *ptep = get_pte(pgdir, la, 0);
    if (ptep != NULL) {
        page_remove_pte(pgdir, la, ptep);
    }
}

//page_insert - 用线性地址la构建页的物理地址映射
// paramemters:
//pgdir：PDT的内核虚拟基址
//page：需要映射的页
//la:线性地址需要映射
//perm：在相关pte中设置的该页的权限
//返回值：始终为0
//注：PT已更改，因此TLB需要失效
int
page_insert(pde_t *pgdir, struct Page *page, uintptr_t la, uint32_t perm) {
    pte_t *ptep = get_pte(pgdir, la, 1);
    if (ptep == NULL) {
        return -E_NO_MEM;
    }
    page_ref_inc(page);
    if (*ptep & PTE_P) {
        struct Page *p = pte2page(*ptep);
        if (p == page) {
            page_ref_dec(page);
        }
        else {
            page_remove_pte(pgdir, la, ptep);
        }
    }
    *ptep = page2pa(page) | PTE_P | perm;
    tlb_invalidate(pgdir, la);
    return 0;
}


//仅当正在编辑的页表是 处理器当前正在使用的页表时，使TLB条目无效。
void
tlb_invalidate(pde_t *pgdir, uintptr_t la) {
    if (rcr3() == PADDR(pgdir)) {
        invlpg((void *)la);
    }
}

static void
check_alloc_page(void) {
    pmm_manager->check();
    cprintf("check_alloc_page() succeeded!\n");
}

static void
check_pgdir(void) {
    assert(npage <= KMEMSIZE / PGSIZE);
    assert(boot_pgdir != NULL && (uint32_t)PGOFF(boot_pgdir) == 0);
    assert(get_page(boot_pgdir, 0x0, NULL) == NULL);

    struct Page *p1, *p2;
    p1 = alloc_page();
    assert(page_insert(boot_pgdir, p1, 0x0, 0) == 0);

    pte_t *ptep;
    assert((ptep = get_pte(boot_pgdir, 0x0, 0)) != NULL);
    assert(pte2page(*ptep) == p1);
    assert(page_ref(p1) == 1);

    ptep = &((pte_t *)KADDR(PDE_ADDR(boot_pgdir[0])))[1];
    assert(get_pte(boot_pgdir, PGSIZE, 0) == ptep);

    p2 = alloc_page();
    assert(page_insert(boot_pgdir, p2, PGSIZE, PTE_U | PTE_W) == 0);
    assert((ptep = get_pte(boot_pgdir, PGSIZE, 0)) != NULL);
    assert(*ptep & PTE_U);
    assert(*ptep & PTE_W);
    assert(boot_pgdir[0] & PTE_U);
    assert(page_ref(p2) == 1);

    assert(page_insert(boot_pgdir, p1, PGSIZE, 0) == 0);
    assert(page_ref(p1) == 2);
    assert(page_ref(p2) == 0);
    assert((ptep = get_pte(boot_pgdir, PGSIZE, 0)) != NULL);
    assert(pte2page(*ptep) == p1);
    assert((*ptep & PTE_U) == 0);

    page_remove(boot_pgdir, 0x0);
    assert(page_ref(p1) == 1);
    assert(page_ref(p2) == 0);

    page_remove(boot_pgdir, PGSIZE);
    assert(page_ref(p1) == 0);
    assert(page_ref(p2) == 0);

    assert(page_ref(pde2page(boot_pgdir[0])) == 1);
    free_page(pde2page(boot_pgdir[0]));
    boot_pgdir[0] = 0;

    cprintf("check_pgdir() succeeded!\n");
}

static void
check_boot_pgdir(void) {
    pte_t *ptep;
    int i;
    for (i = 0; i < npage; i += PGSIZE) {
        assert((ptep = get_pte(boot_pgdir, (uintptr_t)KADDR(i), 0)) != NULL);
        assert(PTE_ADDR(*ptep) == i);
    }

    assert(PDE_ADDR(boot_pgdir[PDX(VPT)]) == PADDR(boot_pgdir));

    assert(boot_pgdir[0] == 0);

    struct Page *p;
    p = alloc_page();
    assert(page_insert(boot_pgdir, p, 0x100, PTE_W) == 0);
    assert(page_ref(p) == 1);
    assert(page_insert(boot_pgdir, p, 0x100 + PGSIZE, PTE_W) == 0);
    assert(page_ref(p) == 2);

    const char *str = "ucore: Hello world!!";
    strcpy((void *)0x100, str);
    assert(strcmp((void *)0x100, (void *)(0x100 + PGSIZE)) == 0);

    *(char *)(page2kva(p) + 0x100) = '\0';
    assert(strlen((const char *)0x100) == 0);

    free_page(p);
    free_page(pde2page(boot_pgdir[0]));
    boot_pgdir[0] = 0;

    cprintf("check_boot_pgdir() succeeded!\n");
}

//perm2str - use string 'u,r,w,-' to present the permission
static const char *
perm2str(int perm) {
    static char str[4];
    str[0] = (perm & PTE_U) ? 'u' : '-';
    str[1] = 'r';
    str[2] = (perm & PTE_W) ? 'w' : '-';
    str[3] = '\0';
    return str;
}

//get_pgtable_items - 在PDT或PT的[left，right]范围内，找到一个连续的线性地址空间
//                  - (left_store*X_SIZE~right_store*X_SIZE) for PDT or PT
//                  - X_SIZE=PTSIZE=4M, if PDT; 
//		     - X_SIZE=PGSIZE=4K, if PT
// paramemters:
//left：没用？？？
//right：表范围的高端
//start：表范围的低端
//table：表的起始地址
//left_store：表的下一个范围的高端指针
//right_store：表的下一个范围的低端的指针
//返回值：0-不是无效项的范围，
//       perm-具有perm权限的有效项范围
static int
get_pgtable_items(size_t left, size_t right, size_t start, uintptr_t *table, size_t *left_store, size_t *right_store) {
    if (start >= right) {
        return 0;
    }
    while (start < right && !(table[start] & PTE_P)) {
        start ++;
    }
    if (start < right) {
        if (left_store != NULL) {
            *left_store = start;
        }
        int perm = (table[start ++] & PTE_USER);
        while (start < right && (table[start] & PTE_USER) == perm) {
            start ++;
        }
        if (right_store != NULL) {
            *right_store = start;
        }
        return perm;
    }
    return 0;
}

//print_pgdir - print the PDT&PT
void
print_pgdir(void) {
    cprintf("-------------------- BEGIN --------------------\n");
    size_t left, right = 0, perm;
    while ((perm = get_pgtable_items(0, NPDEENTRY, right, vpd, &left, &right)) != 0) {
        cprintf("PDE(%03x) %08x-%08x %08x %s\n", right - left,
                left * PTSIZE, right * PTSIZE, (right - left) * PTSIZE, perm2str(perm));
        size_t l, r = left * NPTEENTRY;
        while ((perm = get_pgtable_items(left * NPTEENTRY, right * NPTEENTRY, r, vpt, &l, &r)) != 0) {
            cprintf("  |-- PTE(%05x) %08x-%08x %08x %s\n", r - l,
                    l * PGSIZE, r * PGSIZE, (r - l) * PGSIZE, perm2str(perm));
        }
    }
    cprintf("--------------------- END ---------------------\n");
}

