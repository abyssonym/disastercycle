from randomtools.tablereader import (
    TableObject, get_global_label, tblpath, addresses, get_random_degree,
    get_activated_patches, mutate_normal, shuffle_normal, write_patch)
from randomtools.utils import (
    classproperty, cached_property, get_snes_palette_transformer,
    read_multi, write_multi, utilrandom as random)
from randomtools.interface import (
    get_outfile, get_seed, get_flags, get_activated_codes, activate_code,
    run_interface, rewrite_snes_meta, clean_and_write, finish_interface)
from randomtools.itemrouter import ItemRouter, ItemRouterException
from collections import defaultdict
from os import path
from time import time, sleep, gmtime
from collections import Counter
from itertools import combinations
from sys import argv


VERSION = 1
KINSHIP_FILENAME = 'kinship.bin'
AI_PTR_FILENAME = 'enemy_ai_pointers.txt'
ESKILL_PTR_FILENAME = 'enemy_skill_pointers.txt'

namelibrary = defaultdict(dict)
for nametype in ['demon', 'skill', 'race']:
    filename = '%s_names.txt' % nametype
    with open(path.join(tblpath, filename)) as f:
        for line in f:
            line = line.strip()
            index, name = line.split(' ', 1)
            index = int(index, 0x10)
            namelibrary[nametype][index] = name

ai_pointers = {}
with open(path.join(tblpath, AI_PTR_FILENAME)) as f:
    for line in f:
        line = line.strip()
        pointer, line = line.split()
        assert line[0] == '#'
        length, filename = line.lstrip('#').split(',')
        pointer, length = int(pointer, 0x10), int(length, 0x10)
        name, extension = filename.split('.')
        assert extension == 'bf'
        assert name[:3] == 'ai_'
        name = name[3:]
        ai_pointers[name] = (pointer, length)

eskill_pointers = {}
with open(path.join(tblpath, ESKILL_PTR_FILENAME)) as f:
    for line in f:
        line = line.strip()
        pointer, line = line.split()
        assert line[0] == '#'
        filename = line.lstrip('#')
        pointer = int(pointer, 0x10)
        name, extension = filename.split('.')
        assert extension == 'bin'
        assert name[:3] == 'sk_'
        name = name[3:]
        eskill_pointers[name] = pointer

def get_all_object_skills(objs):
    return sorted(set([s for o in objs for s in o.skills]))


class NakamaParent(TableObject):
    def __repr__(self):
        stats = [self.make_display_line(attr) for attr in self.STATS]
        elements = [self.make_display_line(attr) for attr in self.ELEMENTS]
        ailments = [self.make_display_line(attr) for attr in self.AILMENTS]
        rewards = [self.make_display_line(attr) for attr in self.REWARDS]
        assert len(ailments) == 10
        table = self.make_display_table(
            stats, elements, ailments[:5], ailments[5:], rewards)
        s = '{0:0>3X} {1:0>3X} {2} {3}\n'.format(
            self.index, self.nakama_index,
            self.race_name, self.name.strip('\x00'))
        s += table + '\n'
        return s.strip()

    @cached_property
    def rank(self):
        return self.old_data['lv']

    @cached_property
    def nakama(self):
        return NakamaObject.get(self.index)

    @cached_property
    def enemy(self):
        return EnemyObject.get(self.index)

    @cached_property
    def dsource(self):
        return DSourceObject.get_by_dsource_index(
            self.nakama.old_data['dsource_index'])

    @cached_property
    def dsource_skills(self):
        if self.dsource is None:
            return []
        return self.dsource.old_data['skills']

    @cached_property
    def is_compendium_demon(self):
        return any(self.dsource_skills)

    @cached_property
    def kinship_rankings(self):
        sorted_nakama = sorted(NakamaObject.every,
                               key=lambda n: self.get_kinship(n),
                               reverse=True)
        sorted_nakama = [n for n in sorted_nakama if n.intershuffle_valid]
        if self is self.canonical_version:
            sorted_nakama = [n for n in sorted_nakama
                             if n is n.canonical_version]
        elif self.is_compendium_demon:
            sorted_nakama = [n for n in sorted_nakama if n.is_compendium_demon]
        return sorted_nakama

    @classmethod
    def get_attr_minmax(cls, attr):
        if not hasattr(cls, '_attr_minmax_cache'):
            cls._attr_minmax_cache = {}
        if attr in cls._attr_minmax_cache:
            return cls._attr_minmax_cache[attr]

        values = [o.old_data[attr] for o in cls.every]
        cls._attr_minmax_cache[attr] = (min(values), max(values))
        return cls.get_attr_minmax(attr)

    def get_resistance_flag(self, res, old=False):
        if old:
            val = self.old_data['res_%s_val' % res]
        else:
            val = getattr(self, 'res_%s_val' % res)
        flag = val >> 9
        flag = {0b0000: '',
                0b0010: 'N',
                0b0100: 'W',
                0b0110: 'R',
                0b1000: 'D',
                0b1010: 'S',
                0b110010: '?',
               }[flag]
        return flag

    def get_effective_resistance_value(self, res, old=False):
        if old:
            val = self.old_data['res_%s_val' % res]
        else:
            val = getattr(self, 'res_%s_val' % res)
        val = val & 0x1FF
        flag = self.get_resistance_flag(res, old=old)
        if flag and flag in 'NRD?':
            val = 0
        elif flag == 'W' and val == 100:
            val = 101
        return val

    def make_display_table(self, *columns):
        columns = [c for c in columns if c]
        widest = max([len(line) for column in columns for line in column])
        tallest = max([len(column) for column in columns])

        for column in columns:
            while len(column) < tallest:
                column.append('')

        assert len(set(len(column) for column in columns)) == 1
        s = ''
        for row in zip(*columns):
            line = ' | '.join(('{0:%s}' % widest).format(r) for r in row)
            s += line.rstrip() + '\n'
        return s.rstrip()

    def make_display_line(self, attr):
        if attr in self.ELEMENTS + self.AILMENTS:
            val = self.get_effective_resistance_value(attr)
            flag = self.get_resistance_flag(attr)
            return '{0: <3} {1: >3}{2: >1}'.format(attr.upper(), val, flag)
        else:
            assert attr in self.STATS + self.REWARDS
            return '{0: <2} {1: >5}'.format(
                attr.upper(), getattr(self, attr))

    def _get_kinship_core(self, other):
        assert self.index <= other.index
        if hasattr(NakamaObject, '_kinship_loaded'):
            key = (self.index, other.index)
            if key in NakamaObject._kinship_loaded:
                return NakamaObject._kinship_loaded[key]

        features, weights = [], []

        features.append(
            1 if self.old_data['race'] == other.old_data['race'] else 0)
        weights.append(0.25)
        for attr in ['alignment_ld', 'alignment_lc']:
            a, b = self.old_data[attr], other.old_data[attr]
            if a == b:
                features.append(1)
            elif 1 in [a, b]:
                features.append(0.5)
            else:
                features.append(0)
            weights.append(0.5)

        attrs = self.STATS + ['st_growth', 'vi_growth', 'ag_growth',
                              'lu_growth', 'ma_growth']
        assert 'lv' in attrs
        for attr in attrs:
            a, b = self.old_data[attr], other.old_data[attr]
            low, high = self.get_attr_minmax(attr)
            maxdiff = float(abs(high - low))
            mydiff = abs(a - b)
            features.append(1-(mydiff / maxdiff))
            if attr == 'lv':
                weights.append(1)
            else:
                weights.append(1.0 / (len(attrs)-1))

        rescode_dict = {
                'D': 0.0,
                'R': 0.0,
                'N': 0.1,
                'S': 0.45,
                '':  0.65,
                'W': 1.0,
                }
        for reses in [self.ELEMENTS, self.AILMENTS]:
            for res in reses:
                a = self.get_effective_resistance_value(res, old=True)
                b = other.get_effective_resistance_value(res, old=True)
                maxdiff = 300.0
                mydiff = abs(a - b)
                assert mydiff <= maxdiff
                features.append(1-(mydiff / maxdiff))
                weights.append(1.0 / len(reses))

                if reses is self.ELEMENTS:
                    a = self.get_resistance_flag(res, old=True)
                    b = other.get_resistance_flag(res, old=True)
                    a = rescode_dict[a]
                    b = rescode_dict[b]
                    diff = abs(a-b)
                    features.append(1-diff)
                    weights.append(1.0 / len(reses))

        for i in xrange(16):
            a = self.old_data['inheritance'] & (1 << i)
            b = other.old_data['inheritance'] & (1 << i)
            features.append(1 if a == b else 0)
            weights.append(2.0 / 16.0)

        assert len(weights) == len(features)
        wavg = sum(weights) / len(weights)
        wfs = [(w*f/wavg) for (w, f) in zip(weights, features)]

        distance = sum([wf**2 for wf in wfs]) ** 0.5
        distance = int(round(distance * (10**8)))
        assert distance < (2**32)
        return distance

    def get_kinship(self, other):
        if not hasattr(NakamaObject, '_kinship_loaded'):
            self.load_kinship(KINSHIP_FILENAME)

        if self.index > other.index:
            return other.get_kinship(self)
        if self is not self.nakama:
            return self.nakama.get_kinship(other.nakama)
        if not hasattr(self, '_kinship_cache'):
            self._kinship_cache = {}
        if other.index in self._kinship_cache:
            return self._kinship_cache[other.index]
        assert type(self) is type(other)

        distance = self._get_kinship_core(other)

        if other is not self:
            max_distance = self.get_kinship(self)
            assert max_distance >= distance
            distance = mutate_normal(distance, minimum=0, maximum=max_distance,
                                     random_degree=self.random_degree ** 2,
                                     return_float=True, wide=True)

        self._kinship_cache[other.index] = distance
        return self.get_kinship(other)

    @classmethod
    def save_kinship(cls, filename):
        f = open(path.join(tblpath, filename), 'w+')
        f.close()
        f = open(path.join(tblpath, filename), 'r+b')
        for n1 in NakamaObject.every:
            for n2 in NakamaObject.every:
                if n1.index > n2.index:
                    continue
                kinship = n1._get_kinship_core(n2)
                write_multi(f, n1.index, length=2)
                write_multi(f, n2.index, length=2)
                write_multi(f, kinship, length=4)
        f.close()
        NakamaObject.load_kinship(filename)

    @classmethod
    def load_kinship(cls, filename):
        if not hasattr(NakamaObject, '_kinship_loaded'):
            NakamaObject._kinship_loaded = {}

        try:
            f = open(path.join(tblpath, filename), 'r+b')
        except IOError:
            print 'Generating kinship from scratch. This may take some time...'
            return

        while True:
            pointer = f.tell()
            peek = f.read(8)
            if len(peek) < 8:
                break
            f.seek(pointer)
            index1 = read_multi(f, length=2)
            index2 = read_multi(f, length=2)
            assert index1 <= index2
            kinship = read_multi(f, length=4)
            NakamaObject._kinship_loaded[(index1, index2)] = kinship
        f.close()

    def get_similar_by_kinship(self):
        if not self.intershuffle_valid:
            return self
        candidates = self.kinship_rankings
        index = candidates.index(self)
        index = mutate_normal(index, minimum=0, maximum=len(candidates)-1,
                              random_degree=self.random_degree ** 2, wide=True)
        return candidates[index]

    def get_similar(self, *args, **kwargs):
        return self.get_similar_by_kinship()


class NakamaObject(NakamaParent):
    STATS = ['lv', 'st', 'ma', 'vi', 'ag', 'lu']
    REWARDS = []
    ELEMENTS = ['phy', 'gun', 'fir', 'ice', 'ele', 'win', 'exp', 'cur', 'alm']
    AILMENTS = ['sto', 'rag', 'par', 'bom', 'str',
                'poi', 'cha', 'mut', 'fea', 'sle']

    randomselect_attributes = [
        'race', 'alignment_ld', 'alignment_lc', 'inheritance',
        ('st', 'st_growth'), ('vi', 'vi_growth'), ('ag', 'ag_growth'),
        ('lu', 'lu_growth'), ('ma', 'ma_growth'),
        #('hits_misc', 'hits_count'),
        'attack_element', ('attack_ailment', 'ailment_chance'),
        'res_phy_val', 'res_gun_val', 'res_exp_val', 'res_cur_val',
        'res_fir_val', 'res_ice_val', 'res_ele_val', 'res_win_val',
        'res_sle_val', 'res_poi_val', 'res_par_val', 'res_cha_val',
        'res_mut_val', 'res_sto_val', 'res_fea_val', 'res_str_val',
        'res_bom_val', 'res_rag_val', 'res_alm_val',
        ]
    mutate_attributes = {
        'lv': None, 'st': None, 'ma': None, 'vi': None, 'ag': None, 'lu': None,
        'st_growth': None, 'vi_growth': None, 'ag_growth': None,
        'lu_growth': None, 'ma_growth': None,
        }

    @cached_property
    def name(self):
        return namelibrary['demon'][self.index]

    @cached_property
    def race_name(self):
        return namelibrary['race'][self.race]

    @cached_property
    def intershuffle_valid(self):
        if (self.name.lower() in ['dummy', 'unknown']
                or len(set(self.name)) == 1):
            return False
        if self.old_data['lv'] != self.enemy.old_data['lv']:
            return False
        return True

    @cached_property
    def is_big_boss(self):
        return self is self.canonical_version and not self.is_compendium_demon

    @cached_property
    def sprite(self):
        return self.enemy.sprite

    @cached_property
    def companion_group(self):
        return [n for n in NakamaObject.every if self.name == n.name
                and self.old_data['race'] == n.old_data['race']]

    @cached_property
    def canonical_version(self):
        candidates = self.companion_group
        temp = [c for c in candidates if c.dsource is not None]
        if temp:
            candidates = temp
        temp = [c for c in candidates if c.is_compendium_demon]
        if temp:
            candidates = temp
        return min(candidates, key=lambda n: n.index)

    @cached_property
    def named_enemy(self):
        candidates = [e for e in EnemyObject.every if e.sprite == self.sprite
                      and len(e.name.rstrip('\x00')) >= 2]
        candidates = sorted(set(candidates))
        if self.enemy in candidates:
            return self.enemy
        elif candidates:
            return candidates[0]
        return None

    @cached_property
    def eskills(self):
        enemy = self.named_enemy
        if enemy:
            return enemy.eskills
        return None

    def randomize_skills(self):
        pass

    def randomize(self):
        self.randomize_skills()
        super(NakamaObject, self).randomize()

    @classmethod
    def full_preclean(cls):
        races = sorted(set(n.race for n in NakamaObject))
        for r in races:
            nakamas = [n for n in NakamaObject.ranked
                       if n.is_compendium_demon and n.race == r]
            while True:
                nakamas = sorted(
                    nakamas, key=lambda n: n.lv)
                for n1, n2 in zip(nakamas, nakamas[1:]):
                    n1.lv = max(1, min(99, n1.lv))
                    n2.lv = max(1, min(99, n2.lv))
                    assert n2.lv >= n1.lv
                    if n1.lv == n2.lv == 99:
                        n1.lv = mutate_normal(
                            98, 1, maximum=98,
                            random_degree=n1.random_degree**2, wide=True)
                        break
                    if n1.lv == n2.lv:
                        n2.lv = mutate_normal(
                            n2.lv+1, minimum=n2.lv+1, maximum=99,
                            random_degree=n2.random_degree**2, wide=True)
                        break
                else:
                    break
        super(NakamaObject, cls).full_preclean()

    def preclean(self):
        canon = self.canonical_version
        if self is canon and not self.is_big_boss:
            return

        for attr in self.old_data:
            if attr.startswith('res_'):
                _, res, _ = attr.split('_')
                oldval = self.get_effective_resistance_value(res, old=True)
                canonval = canon.get_effective_resistance_value(res)
                newval = self.get_effective_resistance_value(res)
                if (newval > oldval and canonval > oldval and oldval < 50 and
                        res in ['exp', 'cur', 'sto', 'rag', 'bom', 'sle']):
                    setattr(self, attr, self.old_data[attr])
                elif (oldval < canonval and oldval < 50
                        and res in self.AILMENTS):
                    setattr(self, attr, self.old_data[attr])
                elif canonval <= newval or res in [
                        'phy', 'gun', 'alm', 'fir', 'ice', 'ele', 'win']:
                    setattr(self, attr, getattr(canon, attr))

                newval = self.get_effective_resistance_value(res)
                if (self.is_big_boss and oldval < newval
                        and random.choice([True, False])):
                    setattr(self, attr, self.old_data[attr])
            elif attr in self.STATS:
                old_a, old_b = (self.old_data[attr],
                                self.canonical_version.old_data[attr])
                new_b = getattr(self.canonical_version, attr)

                new_a = old_a * (new_b / float(old_b))
                low, high = self.get_attr_minmax(attr)
                new_a = int(round(max(low, min(high, new_a))))
                setattr(self, attr, new_a)

                if (self.is_big_boss and new_a < old_a
                        and random.choice([True, False])):
                    setattr(self, attr, old_a)
            elif (self.old_data[attr] == canon.old_data[attr]):
                setattr(self, attr, getattr(canon, attr))

    def cleanup(self):
        assert hasattr(EnemyObject, 'precleaned') and EnemyObject.precleaned
        for attr in self.old_data:
            if attr.startswith('res_') and getattr(self, attr) == 0:
                setattr(self, attr, 0x400)

        if AllyObject.flag not in get_flags():
            for attrs in (self.randomselect_attributes +
                          sorted(self.mutate_attributes)):
                if isinstance(attrs, basestring):
                    attrs = [attrs]
                for attr in attrs:
                    if attr not in RaceObject.attributes:
                        setattr(self, attr, self.old_data[attr])

        if RaceObject.flag not in get_flags():
            for attr in RaceObject.attributes:
                setattr(self, attr, self.old_data[attr])


class AllyObject(TableObject):
    flag = 'n'
    flag_description = 'nakama (demon allies)'


class EnemyObject(NakamaParent):
    flag = 'e'
    flag_description = 'enemy stats'

    STATS = ['lv', 'hp', 'mp', 'st', 'ma', 'vi', 'ag', 'lu']
    REWARDS = ['xp', 'mac']
    ELEMENTS = ['phy', 'gun', 'fir', 'ice', 'ele', 'win', 'exp', 'cur', 'alm']
    AILMENTS = ['sto', 'rag', 'par', 'bom', 'str',
                'poi', 'cha', 'mut', 'fea', 'sle']

    mutate_attributes = {
        'xp': None, 'mac': None,
        }

    @classproperty
    def after_order(cls):
        return [NakamaObject]

    @cached_property
    def eskills(self):
        name = self.name.rstrip('\x00')
        return EnemySkillObject.get_by_name(name)

    def preclean(self):
        assert not hasattr(NakamaObject, 'cleaned')
        for attrs in NakamaObject.randomselect_attributes + ['hp', 'mp']:
            if isinstance(attrs, basestring):
                attrs = [attrs]
            for attr in attrs:
                if not hasattr(self, attr):
                    continue

                if hasattr(self.nakama, attr):
                    nattr = attr
                else:
                    nattr = {'hp': 'vi',
                             'mp': 'ma',
                             }[attr]

                old_a, old_b = (self.old_data[attr],
                                self.nakama.old_data[nattr])
                new_b = getattr(self.nakama, nattr)
                if attr.startswith('res_'):
                    setattr(self, attr, new_b)
                elif attr in self.STATS:
                    new_a = old_a * (new_b / float(old_b))
                    low, high = self.get_attr_minmax(attr)
                    new_a = int(round(max(low, min(high, new_a))))
                    setattr(self, attr, new_a)
                elif old_a == old_b and attr == nattr:
                    setattr(self, attr, new_b)

        # nerf early zone enemies
        if self.old_data['lv'] < 10:
            for attr in self.STATS:
                old, new = self.old_data[attr], getattr(self, attr)
                if new > old:
                    if self.old_data['lv'] == 1:
                        ratio = 0
                    else:
                        ratio = (self.old_data['lv'] / 10.0) ** 2
                    balanced = (new*ratio) + (old*(1-ratio))
                    assert old <= balanced <= new
                    setattr(self, attr, int(round(balanced)))

    def cleanup(self):
        if EnemyObject.flag not in get_flags():
            for attr in self.STATS:
                setattr(self, attr, self.old_data[attr])

        for attr in self.old_data:
            if attr.startswith('res_') and getattr(self, attr) == 0:
                setattr(self, attr, 0x400)

        if 'easymodo' in get_activated_codes():
            for stat in self.STATS:
                setattr(self, stat, 1)
            self.mp = 9999
            self.hp = self.old_data['hp']


class EnemySkillObject(TableObject):
    flag = 's'
    flag_description = 'demon skills'

    @classmethod
    def get_by_name(cls, name):
        if name in eskill_pointers:
            return EnemySkillObject.get_by_pointer(eskill_pointers[name])
        return None


class DSourceObject(TableObject):
    flag = 's'

    @classmethod
    def get_by_dsource_index(cls, index):
        candidates = [d for d in DSourceObject.every
                      if d.dsource_index == index]
        if len(candidates) == 0:
            return None
        assert len(candidates) == 1
        return candidates[0]


class RaceObject(TableObject):
    flag = 'f'
    flag_description = 'demon races (fusion recipes) and alignments'
    attributes = ['race', 'alignment_ld', 'alignment_lc']


if __name__ == '__main__':
    try:
        print ('You are using the Shin Megami Tensei: Strange Journey '
               'randomizer version %s.' % VERSION)
        print

        ALL_OBJECTS = [g for g in globals().values()
                       if isinstance(g, type) and issubclass(g, TableObject)
                       and g not in [TableObject]]

        codes = {'easymodo': ['easymodo'],
                }

        run_interface(ALL_OBJECTS, snes=False, codes=codes,
                      custom_degree=True)

        #NakamaObject.save_kinship('kinship.bin')

        clean_and_write(ALL_OBJECTS)

        #for n in NakamaObject.every:
        #    if n.intershuffle_valid:
        #        print n
        #        print '-' * 79

        finish_interface()

    except Exception, e:
        print 'ERROR: %s' % e
        raw_input('Press Enter to close this program. ')
