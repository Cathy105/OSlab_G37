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
 *
 * The TSS may reside anywhere in memory. A special segment register called
 * the Task Register (TR) holds a segment selector that points a valid TSS
 * segment descriptor which resides in the GDT. Therefore, to use a TSS
 * the following must be done in function gdt_init:
 *   - create a TSS descriptor entry in GDT
 *   - add enough information to the TSS in memory as needed
 *   - load the TR register with a segment selector for that segment
 *
 * There are several fileds in TSS for specifying the new stack pointer when a
 * privilege level change happens. But only the fields SS0 and ESP0 are useful
 * in our os kernel.
 *
 * The field SS0 contains the stack segment selector for CPL = 0, and the ESP0
 * contains the new ESP value for CPL = 0. When an interrupt happens in protected
 * mode, the x86 CPU will look in the TSS for SS0 and ESP0 and load their value
 * into SS and ESP respectively.
 * */
 /* *

*任务状态段：

*

*TSS可以驻留在内存中的任何位置。称为任务寄存器（TR）的特殊段寄存器包含一个段选择器，该选择器指向驻留在GDT中的有效TSS段描述符。因此，要使用TSS，必须在函数gdt\u init中执行以下操作：-在gdt中创建TSS描述符条目-根据需要向内存中的TSS添加足够的信息-使用该段的段选择器加载TR寄存器

*TSS中有几个文件用于在发生权限级别更改时指定新的堆栈指针。但是在我们的操作系统内核中只有SS0和ESP0字段是有用的。

*

*字段SS0包含CPL=0的堆栈段选择器，ESP0包含CPL=0的新ESP值。在保护模式下发生中断时，x86 CPU将在TSS中查找SS0和ESP0，并将其值分别加载到SS和ESP中。

* */
static struct taskstate ts = {0};

// virtual address of physicall page array物理调用页数组的虚拟地址
struct Page *pages;
// amount of physical memory (in pages)物理内存量（页）
size_t npage = 0;

// virtual address of boot-time page directory启动时页目录的虚拟地址
extern pde_t __boot_pgdir;
pde_t *boot_pgdir = &__boot_pgdir;
// physical address of boot-time page directory启动时页目录的物理地址
uintptr_t boot_cr3;

// physical memory management物理内存管理
const struct pmm_manager *pmm_manager;

/* *
 * The page directory entry corresponding to the virtual address range
 * [VPT, VPT + PTSIZE) points to the page directory itself. Thus, the page
 * directory is treated as a page table as well as a page directory.
 *
 * One result of treating the page directory as a page table is that all PTEs
 * can be accessed though a "virtual page table" at virtual address VPT. And the
 * PTE for number n is stored in vpt[n].
 *
 * A second consequence is that the contents of the current page directory will
 * always available at virtual address PGADDR(PDX(VPT), PDX(VPT), 0), to which
 * vpd is set bellow.
 * */
 /* *

*与虚拟地址范围[VPT，VPT+PTSIZE]对应的页目录条目指向页目录本身。因此，页目录被视为页表和页目录。

*

*将页目录视为页表的一个结果是，可以通过虚拟地址VPT处的“虚拟页表”访问所有pte。数字n的PTE存储在vpt[n]中。

*

*第二个结果是当前页目录的内容将始终在虚拟地址PGADDR（PDX（VPT），PDX（VPT），0）处可用，vpd设置如下。

* */
pte_t * const vpt = (pte_t *)VPT;
pde_t * const vpd = (pde_t *)PGADDR(PDX(VPT), PDX(VPT), 0);

/* *
 * Global Descriptor Table:
 *
 * The kernel and user segments are identical (except for the DPL). To load
 * the %ss register, the CPL must equal the DPL. Thus, we must duplicate the
 * segments for the user and the kernel. Defined as follows:
 *   - 0x0 :  unused (always faults -- for trapping NULL far pointers)
 *   - 0x8 :  kernel code segment
 *   - 0x10:  kernel data segment
 *   - 0x18:  user code segment
 *   - 0x20:  user data segment
 *   - 0x28:  defined for tss, initialized in gdt_init
 * */
 /* *

*全局描述符表：

*

*内核和用户段是相同的（除了DPL）。要加载%ss寄存器，CPL必须等于DPL。因此，我们必须为用户和内核复制段。定义如下：

*-0x0:未使用（总是错误--用于捕获空远指针）

*-0x8：内核代码段

*-0x10：内核数据段

*-0x18：用户代码段

*-0x20：用户数据段

*-0x28:为tss定义，在gdt\u init中初始化

* */


static struct segdesc gdt[] = {
    SEG_NULL,
    [SEG_KTEXT] = SEG(STA_X | STA_R, 0x0, 0xFFFFFFFF, DPL_KERNEL),
    [SEG_KDATA] = SEG(STA_W, 0x0, 0xFFFFFFFF, DPL_KERNEL),
    [SEG_UTEXT] = SEG(STA_X | STA_R, 0x0, 0xFFFFFFFF, DPL_USER),
    [SEG_UDATA] = SEG(STA_W, 0x0, 0xFFFFFFFF, DPL_USER),
    [SEG_TSS]   = SEG_NULL,
};

static struct pseudodesc gdt_pd = {
    sizeof(gdt) - 1, (uintptr_t)gdt
};

static void check_alloc_page(void);
static void check_pgdir(void);
static void check_boot_pgdir(void);

/* *
 * lgdt - load the global descriptor table register and reset the
 * data/code segement registers for kernel.
 * */
 /* *

*lgdt—加载全局描述符表寄存器并重置内核的数据/代码段寄存器。

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
 * load_esp0 - change the ESP0 in default task state segment,
 * so that we can use different kernel stack when we trap frame
 * user to kernel.
 * */
 /* *

*load_esp0-更改默认任务状态段中的esp0，以便在将帧用户捕获到内核时可以使用不同的内核堆栈。

* */
void
load_esp0(uintptr_t esp0) {
    ts.ts_esp0 = esp0;
}

/* gdt_init - initialize the default GDT and TSS *//*gdt_init-初始化默认的gdt和TSS*/


static void
gdt_init(void) {
    // set boot kernel stack and default SS0设置引导内核堆栈和默认SS0
    load_esp0((uintptr_t)bootstacktop);
    ts.ts_ss0 = KERNEL_DS;

    // initialize the TSS filed of the gdt初始化gdt的TSS文件
    gdt[SEG_TSS] = SEGTSS(STS_T32A, (uintptr_t)&ts, sizeof(ts), DPL_KERNEL);

    // reload all segment registers重新加载所有段寄存器
    lgdt(&gdt_pd);

    // load the TSS加载TSS
    ltr(GD_TSS);
}

//init_pmm_manager - initialize a pmm_manager instance初始化pmm\u管理器-初始化pmm\u管理器实例
static void
init_pmm_manager(void) {
    pmm_manager = &default_pmm_manager;
    cprintf("memory management: %s\n", pmm_manager->name);
    pmm_manager->init();
}

//init_memmap - call pmm->init_memmap to build Page struct for free memory  
//init\u memmap-调用pmm->init\u memmap为空闲内存构建页面结构
static void
init_memmap(struct Page *base, size_t n) {
    pmm_manager->init_memmap(base, n);
}

//alloc_pages - call pmm->alloc_pages to allocate a continuous n*PAGESIZE memory 
//alloc\u pages-调用pmm->alloc\u页面以分配连续n*PAGESIZE内存
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
//free\u pages-调用pmm->free\u pages来释放一个连续的n*PAGESIZE内存
void
free_pages(struct Page *base, size_t n) {
    bool intr_flag;
    local_intr_save(intr_flag);
    {
        pmm_manager->free_pages(base, n);
    }
    local_intr_restore(intr_flag);
}

//nr_free_pages - call pmm->nr_free_pages to get the size (nr*PAGESIZE) 
//of current free memory
//nr\u free\u pages-调用pmm->nr\u free\u pages获取当前可用内存的大小（nr*PAGESIZE）
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

/* pmm_init - initialize the physical memory management */
/*pmm\u init-初始化物理内存管理*/
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
// parameters
//  la:   linear address of this memory need to map (after x86 segment map)
//  size: memory size
//  pa:   physical address of this memory
//  perm: permission of this memory  
//boot\u map\u segment-设置并启用分页机制参数
//la：这个内存的线性地址需要映射（在x86段映射之后）
//大小：内存大小
//pa：这个内存的物理地址
//perm:此内存的权限
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

//boot_alloc_page - allocate one page using pmm->alloc_pages(1) 
// return value: the kernel virtual address of this allocated page
//note: this function is used to get the memory for PDT(Page Directory Table)&PT(Page Table)
//boot\u alloc\u page-使用pmm->alloc\u pages（1）分配一个页面
//返回值：此分配页的内核虚拟地址
//注意：此函数用于获取PDT（页目录表）和PT（页表）的内存
static void *
boot_alloc_page(void) {
    struct Page *p = alloc_page();
    if (p == NULL) {
        panic("boot_alloc_page failed.\n");
    }
    return page2kva(p);
}

//pmm_init - setup a pmm to manage physical memory, build PDT&PT to setup paging mechanism 
//         - check the correctness of pmm & paging mechanism, print PDT&PT
//pmm_init-设置pmm来管理物理内存，构建PDT&PT来设置分页机制-检查pmm&paging机制的正确性，打印PDT&PT
void
//////////////////////////////////////////////////////////////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////

pmm_init(void) {//////////////////////////////////////////////////////////////////////////////
    // We've already enabled paging已经启用了分页
    boot_cr3 = PADDR(boot_pgdir);//6

    //We need to alloc/free the physical memory (granularity is 4KB or other size). 
    //So a framework of physical memory manager (struct pmm_manager)is defined in pmm.h
    //First we should init a physical memory manager(pmm) based on the framework.
    //Then pmm can alloc/free the physical memory. 
    //Now the first_fit/best_fit/worst_fit/buddy_system pmm are available.
//我们需要分配/释放物理内存（粒度为4KB或其他大小）。
//因此，在pmm.h中定义了一个物理内存管理器框架（struct-pmm\u-manager）
//首先，我们应该基于这个框架初始化一个物理内存管理器（pmm）。
//然后pmm可以分配/释放物理内存。
//现在提供了first\u fit/best\u fit/worst\u fit/buddy\u system pmm。
    init_pmm_manager();//1

    // detect physical memory space, reserve already used memory,
    // then use pmm->init_memmap to create free page list
    //检测物理内存空间，保留已用内存，
    //然后使用pmm->init\u memmap创建自由页面列表
    page_init();//2

    //use pmm->check to verify the correctness of the alloc/free function in a pmm
    //使用pmm->check验证pmm中alloc/free函数的正确性
    check_alloc_page();//3

    check_pgdir();//3

    static_assert(KERNBASE % PTSIZE == 0 && KERNTOP % PTSIZE == 0);//check3

    // recursively insert boot_pgdir in itself
    // to form a virtual page table at virtual address VPT
    //递归地将boot\ u pgdir插入到其自身中，以在虚拟地址VPT处形成虚拟页表
    boot_pgdir[PDX(VPT)] = PADDR(boot_pgdir) | PTE_P | PTE_W;//4

    // map all physical memory to linear memory with base linear addr KERNBASE
    // linear_addr KERNBASE ~ KERNBASE + KMEMSIZE = phy_addr 0 ~ KMEMSIZE
//使用base linear addr KERNBASE将所有物理内存映射到线性内存
//线性地址KERNBASE~KERNBASE+KMEMSIZE=phy地址0~KMEMSIZE
    boot_map_segment(boot_pgdir, KERNBASE, KMEMSIZE, 0, PTE_W);//5

    // Since we are using bootloader's GDT,
    // we should reload gdt (second time, the last time) to get user segments and the TSS
    // map virtual_addr 0 ~ 4G = linear_addr 0 ~ 4G
    // then set kernel stack (ss:esp) in TSS, setup TSS in gdt, load TSS
//因为我们使用的是引导加载程序的GDT，
//我们应该重新加载gdt（第二次，最后一次）以获得用户段和TSS
//映射虚拟地址0~4G=线性地址0~4G
//然后在TSS中设置内核堆栈（ss:esp），在gdt中设置TSS，加载TSS
    gdt_init();//7

    //now the basic virtual memory map(see memalyout.h) is established.
    //check the correctness of the basic virtual memory map.
//现在基本的虚拟内存映射（参见memalyout.h）已经建立。
//检查基本虚拟内存映射的正确性。    
    check_boot_pgdir();//9

    print_pgdir();//10

}

//get_pte - get pte and return the kernel virtual address of this pte for la
//        - if the PT contians this pte didn't exist, alloc a page for PT
// parameter:
//  pgdir:  the kernel virtual base address of PDT
//  la:     the linear address need to map
//  create: a logical value to decide if alloc a page for PT
// return vaule: the kernel virtual address of this pte
//get_pte-get pte并为la返回此pte的内核虚拟地址
//-如果PT contians this pte不存在，请为PT分配一个页面
//参数：
//pgdir：PDT的内核虚拟基址
//la:线性地址需要映射
//create：一个逻辑值，用于决定是否为PT分配一个页面
//return vaule：这个pte的内核虚拟地址
pte_t *
get_pte(pde_t *pgdir, uintptr_t la, bool create) {
    /* LAB2 EXERCISE 2: YOUR CODE
     *
     * If you need to visit a physical address, please use KADDR()
     * please read pmm.h for useful macros
     *
     * Maybe you want help comment, BELOW comments can help you finish the code
     *
     * Some Useful MACROs and DEFINEs, you can use them in below implementation.
     * MACROs or Functions:
     *   PDX(la) = the index of page directory entry of VIRTUAL ADDRESS la.
     *   KADDR(pa) : takes a physical address and returns the corresponding kernel virtual address.
     *   set_page_ref(page,1) : means the page be referenced by one time
     *   page2pa(page): get the physical address of memory which this (struct Page *) page  manages
     *   struct Page * alloc_page() : allocation a page
     *   memset(void *s, char c, size_t n) : sets the first n bytes of the memory area pointed by s
     *                                       to the specified value c.
     * DEFINEs:
     *   PTE_P           0x001                   // page table/directory entry flags bit : Present
     *   PTE_W           0x002                   // page table/directory entry flags bit : Writeable
     *   PTE_U           0x004                   // page table/directory entry flags bit : User can access
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
/*LAB2练习2：你的代码
*如果您需要访问物理地址，请使用KADDR（）
*有关有用的宏，请阅读pmm.h
*也许你想要帮助注释，下面的注释可以帮助你完成代码
*
*一些有用的宏和定义，您可以在下面的实现中使用它们。
*宏或函数：
*PDX（la）=虚拟地址la的页目录项索引。
*KADDR（pa）：获取物理地址并返回相应的内核虚拟地址。
*set\ page\ ref（第1页）：表示该页被一次引用
*page2pa（page）：获取这个（struct page*）页管理的内存的物理地址
*结构页*分配页（）：分配页
*memset（void*s，char c，size\t n）：设置s指向的内存区域的前n个字节
*至规定值c。
*定义：
*PTE\u P 0x001//页表/目录条目标志位：存在
*PTE\u W 0x002//页表/目录项标志位：可写
*PTE_0x004//页表/目录条目标志位：用户可以访问
*/
//#如果0
//pde_t*pdep=NULL；//（1）查找页目录项
//如果（0）{//（2）检查条目是否不存在
//（3）检查是否需要创建，然后为页表分配页
//注意：此页用于页表，不用于公共数据页
//（4）设置页面引用
//uintptr\u t pa=0；//（5）获取页的线性地址
//（6）使用memset清除页面内容
//（7）设置页面目录项的权限
//}
//return NULL；//（8）返回页表条目

    pde_t *pdep = &pgdir[PDX(la)];
    if (!(*pdep & PTE_P)) {
        struct Page *page;
        if (!create || (page = alloc_page()) == NULL) {
            return NULL;
        }
        set_page_ref(page, 1);
        uintptr_t pa = page2pa(page);
        memset(KADDR(pa), 0, PGSIZE);
        *pdep = pa | PTE_U | PTE_W | PTE_P;
    }
    return &((pte_t *)KADDR(PDE_ADDR(*pdep)))[PTX(la)];
}

//get_page - get related Page struct for linear address la using PDT pgdir
//get_page-使用PDT pgdir获取线性地址la的相关页结构
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

//page_remove_pte - free an Page sturct which is related linear address la
//                - and clean(invalidate) pte which is related linear address la
//note: PT is changed, so the TLB need to be invalidate 
//page_remove_pte-释放与线性地址la相关的页结构
//-和清除（使无效）与线性地址la相关的pte
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
/*LAB2练习3：你的代码
*
*请检查ptep是否有效，如果更新映射，则必须手动更新tlb
*
*也许你想要帮助注释，下面的注释可以帮助你完成代码
*
*一些有用的宏和定义，您可以在下面的实现中使用它们。
*宏或函数：
*结构页*Page pte2page（*ptep）：从ptep的值中获取相应的页
*免费页面：免费页面
*页码：减少页码->参考。注意：ff页码->参考==0，则此页应为自由页。
*tlb_invalidate（pde_t*pgdir，uintptr_t la）：使tlb条目无效，但仅当页表
*已编辑的是处理器当前正在使用的。
*定义：
*PTE\u P 0x001//页表/目录条目标志位：存在
*/
//#如果0
//如果（0）{//（1），请检查页目录是否存在
//struct Page*Page=NULL；//（2）找到与pte对应的页
//（3） 减少页面引用
//（4） 当页面引用达到0时释放此页面
//（5） 清除第二页表格条目
//（6） 嵌入式tlb
//}
//#结束
    if (*ptep & PTE_P) {//（1）请检查页目录是否存在
    //检查页表项pte的最低位PTE_P的值，若为0，则说明对应的物理页不存在，此时直接返回即可
        struct Page *page = pte2page(*ptep);//（2）找到与pte对应的页
        if (page_ref_dec(page) == 0) {//（3） 减少页面引用//判断Page的ref的值是否为0
            free_page(page);//（4） 当页面引用达到0时释放此页面
            //若为0，则说明此时没有任何逻辑地址被映射到此物理地址，换句话说当前物理页已没人使用，因此调用free_page函数回收此物理页
        }
        *ptep = 0;//（5） 清除第二页表格条目
        //将对应的页表项pte清零，表明此逻辑地址无对应的物理地址。
        tlb_invalidate(pgdir, la);//（6） 嵌入式tlb
        //调用tlb_invalidate函数去使能TLB中当前逻辑地址对应的条目。
    }
}

//page_remove - free an Page which is related linear address la and has an validated pte
//page_remove-free一个与线性地址la相关并具有已验证的pte的页
void
page_remove(pde_t *pgdir, uintptr_t la) {
    pte_t *ptep = get_pte(pgdir, la, 0);
    if (ptep != NULL) {
        page_remove_pte(pgdir, la, ptep);
    }
}

//page_insert - build the map of phy addr of an Page with the linear addr la
// paramemters:
//  pgdir: the kernel virtual base address of PDT
//  page:  the Page which need to map
//  la:    the linear address need to map
//  perm:  the permission of this Page which is setted in related pte
// return value: always 0
//note: PT is changed, so the TLB need to be invalidate 
//第u页插入-用线性addr la构建页面的phy addr映射
//参数：
//pgdir：PDT的内核虚拟基地址
//页码：需要映射的页面
//la：需要映射的线性地址
//perm：此页面的权限，设置在相关pte中
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

// invalidate a TLB entry, but only if the page tables being
// edited are the ones currently in use by the processor.
//使TLB条目无效，但仅当页表
//已编辑的是处理器当前正在使用的。
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
//perm2str-使用字符串'u，r，w，-'表示权限
static const char *
perm2str(int perm) {
    static char str[4];
    str[0] = (perm & PTE_U) ? 'u' : '-';
    str[1] = 'r';
    str[2] = (perm & PTE_W) ? 'w' : '-';
    str[3] = '\0';
    return str;
}

//get_pgtable_items - In [left, right] range of PDT or PT, find a continuous linear addr space
//                  - (left_store*X_SIZE~right_store*X_SIZE) for PDT or PT
//                  - X_SIZE=PTSIZE=4M, if PDT; X_SIZE=PGSIZE=4K, if PT
// paramemters:
//  left:        no use ???
//  right:       the high side of table's range
//  start:       the low side of table's range
//  table:       the beginning addr of table
//  left_store:  the pointer of the high side of table's next range
//  right_store: the pointer of the low side of table's next range
// return value: 0 - not a invalid item range, perm - a valid item range with perm permission 
//在PDT或PT的[left，right]范围内，找到一个连续的线性addr空间
//-（左存储*X大小~右存储*X大小）用于PDT或PT
//-X_SIZE=PTSIZE=4M，若为PDT；X_SIZE=PGSIZE=4K，若为PT
//参数：
//左：没用？？？
//右：桌子范围的高端
//开始：桌子范围的低端
//表：表的起始地址
//left\ u store：表的下一个范围的高端指针
//右存储：表的下一个范围的低端的指针
//返回值：0-不是无效的项范围，perm-具有perm权限的有效项范围
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


//当页目录项或页表项有效时（即页目录项或页表项有具体的数值而非全0），数据结构pages与页目录项和页表项有对应关系。pages每一项记录一个物理页的信息，而每个页目录项记录一个页表的信息，每个页表项则记录一个物理页的信息。假设系统中共有N个物理页，那么pages共有N项，第i项对应第i个物理页的信息。而页目录项和页表项的第31~12位构成的20位数分别对应一个物理页编号，因此也就和pages的对应元素一一对应。
