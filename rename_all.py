import os
import re
import json

def global_rename_and_update_json():
    declaration_re = re.compile(r'^(?:private\s+|protected\s+|noncomputable\s+|) *(?:@[^\n]+\s+)*(theorem|lemma)\s+([a-zA-Z0-9_.]+)(.*)')
    
    rename_map = {}
    for root, dirs, files in os.walk('CKSD'):
        for file in files:
            if not file.endswith('.lean'):
                continue
            path = os.path.join(root, file)
            with open(path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            for line in content.split('\n'):
                m = declaration_re.match(line)
                if m:
                    full_name = m.group(2)
                    parts = full_name.split('.')
                    decl_name = parts[-1]
                    if re.search(r'[A-Z][a-z]', decl_name) and not decl_name.startswith('Is') and not decl_name.startswith('Has'):
                        s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', decl_name)
                        snake_name = re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()
                        snake_name = re.sub('_+', '_', snake_name)
                        if decl_name != snake_name:
                            rename_map[decl_name] = snake_name

    to_remove = []
    for k in rename_map:
        if k.startswith('Matrix') or k.startswith('Submodule') or k.startswith('Finset') or k.startswith('Measure') or k.startswith('Continuous') or k.startswith('EuclideanSpace') or k.startswith('Real') or k.startswith('Complex'):
            to_remove.append(k)
    for k in to_remove:
        del rename_map[k]

    print(f"Found {len(rename_map)} declarations to rename.")
    sorted_keys = sorted(rename_map.keys(), key=len, reverse=True)
    
    # 2. apply replacements
    for root, dirs, files in os.walk('CKSD'):
        for file in files:
            if not file.endswith('.lean'):
                continue
            path = os.path.join(root, file)
            with open(path, 'r', encoding='utf-8') as f:
                content = f.read()
                
            modified = False
            for old_name in sorted_keys:
                if old_name in content:
                    pattern = r"(?<![a-zA-Z0-9_])" + re.escape(old_name) + r"(?![a-zA-Z0-9_'])"
                    new_content, count = re.subn(pattern, rename_map[old_name], content)
                    if count > 0:
                        content = new_content
                        modified = True
                        
            if modified:
                with open(path, 'w', encoding='utf-8') as f:
                    f.write(content)

    # 3. Update formalization.json
    with open("formalization.json") as f:
        data = json.load(f)

    changed = False
    for decl in data.get('declarations', []):
        name = decl['name']
        parts = name.split('.')
        base = parts[-1]
        if base in rename_map:
            parts[-1] = rename_map[base]
            decl['name'] = '.'.join(parts)
            changed = True

    if changed:
        with open("formalization.json", "w") as f:
            json.dump(data, f, indent=2)
            f.write('\n')
        print("Updated formalization.json")

os.chdir('/ufs/braams/lean-CKSD')
global_rename_and_update_json()
